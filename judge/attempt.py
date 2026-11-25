#!/usr/bin/env python3
"""attempt.py — the judge of the soundness-lemma benchmark.  hol4/delta3/harness · Day 2 (2026-11-24)

  attempt.sh <statement-id> <proof-script-file> <agent-name> --family claude|gpt|other --model <name>
             [--tokens N] [--time-limit S] [--cpu-limit S] [--mem-limit-gb G] [--notes TEXT]
             [--host HOST [--port P] [--user U]] [--refute]

--refute: the script claims the statement is FALSE: it must save a theorem named <id>_refuted whose conclusion
is exactly  ~(the right-hand side of <id>_def)  — the statement alone, closed — judged like a proof
(outcome "refuted"). RUN.json, when present, caps attempts per statement and family (RUN-PROTOCOL.md).

Two model families attempt the same statements, each blind to the other's scripts.  The caller says
which family and model an attempt belongs to; the harness records both and keeps the script and all
logs under work/<family>/<id>-<n>/.  A family must not read the other family's directory.
Attempts are numbered per statement and family.  No attempt runs unless the statements, the
dependency table and the base theories still have the hashes written in the freeze file
(FREEZE-2.json when it exists — the re-keyed benchmark — else FREEZE.json; freeze.py).

The script must be a complete HOL4 script whose first code line is `Theory attempt` and which
saves a theorem named <statement-id>.  It is copied into a fresh directory and built with Holmake
against the pinned HOL (HOLDIR) and the prebuilt base theories (base/), by judgelib.py:
  - on this Mac (default): under macOS sandbox-exec with sandbox.sb — no network, no file writes
    outside the attempt's directory (and Poly/ML's /var/tmp/MLTEMP* files), no programs but the
    toolchain, no signals outside the sandbox, no Mach service lookups;
  - with --host: on a Linux pod, by pod/runner.py, under pod/jail (seccomp: no sockets but unix ones;
    Landlock where the kernel has it: no writes outside the attempt's directory and /tmp), as an
    unprivileged slot user, in a new network namespace when the container allows one.
Limits on every attempt: wall time (--time-limit, default 600 s), CPU time per process
(--cpu-limit, default twice the wall limit), resident memory of all its processes together
(--mem-limit-gb, default 6).

PROVED is decided only when ALL of these hold (judgelib.decide); anything else is recorded with its reason:
  1. text      the script contains none of the tokens in judgelib.DENY_RAW (comments included) and,
               outside comments, none of judgelib.DENY_CODE;
  2. build     Holmake exits 0 within the limits (else outcome failed / timeout);
  3. exact     the saved theorem's conclusion is alpha-equal to the recorded goal
               (dep1 /\\ ... /\\ depk ==> statement, or the statement alone), built by the judge
               from delta3_stmtsTheory — so a weaker or different statement under the same
               name is refused; constants are compared by theory and name;
  4. no hyps   the theorem has no hypotheses;
  5. tags      its oracle tags are a subset of {DISK_THM} and its axiom tags are empty;
  6. axioms    the attempt theory declares no axiom;
  7. base      the base theories' files have the same sha256 after the attempt as before.
The judge is a separate HOL process that loads the saved theory; it does not trust the build log.

NOT covered (JUDGE.json "not_covered"): the attempt's ML code runs inside the processes that write
the theory file and the judge's answer, and HOL4 trusts its own disk format.  A deliberate forgery
from inside the build is stopped only by the token check — a filter, not a proof — and by reading
every proved script.  The isolation protects the machine, the records and the other attempts.

Every attempt appends one line to attempts.jsonl: statement, attempt number, agent, outcome
(proved | refuted | failed | timeout | refused), reason, wall seconds, CPU seconds, peak memory, the limits,
the isolation, the host, sha256 of the script, HOL commit, the judge's code digest, tokens when supplied.
"""
import sys, os, re, json, time, hashlib, shutil, subprocess, argparse, fcntl, socket, platform

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import judgelib

BASE = os.path.join(HERE, 'base')
HOLDIR = os.environ.get('HOLDIR') or os.path.expanduser(json.load(open(os.path.join(HERE, 'PIN.json')))['hol_dir_mac'])   # the one pin
LOG = os.path.join(HERE, 'attempts.jsonl')
LOCK = os.path.join(HERE, '.attempts.lock')


def freeze_file():
    for f in ('FREEZE-2.json', 'FREEZE.json'):
        p = os.path.join(HERE, f)
        if os.path.exists(p):
            return f, json.load(open(p))
    return None, None


class Locked:
    def __enter__(self):
        self.f = open(LOCK, 'a'); fcntl.flock(self.f, fcntl.LOCK_EX); return self
    def __exit__(self, *a):
        fcntl.flock(self.f, fcntl.LOCK_UN); self.f.close()


def wait_for_free_mac(max_s):
    """The Mac is shared: never two Holmake runs at once. Waits while any other HOL build or HOL
    process runs on this machine (any user, any session); returns the seconds waited, or None when
    max_s passed and the machine is still busy."""
    t0 = time.time()
    while True:
        out = subprocess.run(['ps', '-A', '-o', 'pid=,comm='], capture_output=True, text=True).stdout
        busy = [l for l in out.splitlines() if os.path.basename(l.split(None, 1)[-1].strip()) in ('Holmake', 'hol', 'buildheap')]
        if not busy:
            return round(time.time() - t0, 1)
        if time.time() - t0 > max_s:
            return None
        time.sleep(10)


def reserve(family, lemma):
    """the attempt number and its fresh directory, reserved atomically (several attempts may run at once)"""
    with Locked():
        prev = [json.loads(l) for l in open(LOG)] if os.path.exists(LOG) else []
        n = 1 + sum(1 for r in prev if r['lemma'] == lemma and r.get('family') == family)
        fam = os.path.join(HERE, 'work', family)
        os.makedirs(fam, exist_ok=True)
        while True:
            work = os.path.join(fam, '%s-%d' % (lemma, n))
            try:
                os.mkdir(work)
                return n, work
            except FileExistsError:
                n += 1


def append(rec):
    with Locked():
        seq = 1 + (sum(1 for _ in open(LOG)) if os.path.exists(LOG) else 0)
        rec = dict(seq=seq, **rec)
        open(LOG, 'a').write(json.dumps(rec) + '\n')
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('lemma'); ap.add_argument('script'); ap.add_argument('agent')
    ap.add_argument('--family', required=True, choices=['claude', 'gpt', 'other'])
    ap.add_argument('--model', required=True)
    ap.add_argument('--tokens', type=int, default=None)
    ap.add_argument('--time-limit', type=int, default=int(os.environ.get('ATTEMPT_TIME_LIMIT', '600')))
    ap.add_argument('--cpu-limit', type=int, default=None)
    ap.add_argument('--mem-limit-gb', type=float, default=float(os.environ.get('ATTEMPT_MEM_LIMIT_GB', '6')))
    ap.add_argument('--notes', default=None)
    ap.add_argument('--host', default=os.environ.get('JUDGE_HOST'))
    ap.add_argument('--port', default=os.environ.get('JUDGE_PORT', '22'))
    ap.add_argument('--user', default=os.environ.get('JUDGE_USER', 'root'))
    ap.add_argument('--isolation', default='mac' if platform.system() == 'Darwin' else None,
                    choices=['mac', 'none'], help='local runs only; "none" is for tests of the harness itself and is recorded')
    ap.add_argument('--refute', action='store_true', help='the script proves  ~statement  as a theorem named <id>_refuted')
    ap.add_argument('--skip-text-check', action='store_true', help='for the harness controls only: lets the tag check be shown alone')
    a = ap.parse_args()
    if not re.match(r'^[A-Za-z0-9_.-]{1,64}$', a.agent) or not re.match(r'^[A-Za-z0-9_.:-]{1,64}$', a.model):
        sys.exit('agent and model names: letters, digits, _ . - (and : in the model), at most 64')
    lemmas = json.load(open(os.path.join(HERE, 'lemmas.json')))
    if a.lemma not in lemmas: sys.exit('unknown statement id ' + a.lemma)
    deps = lemmas[a.lemma]['deps']
    import freeze
    fname, frozen = freeze_file()
    if frozen is None: sys.exit('not frozen: run freeze.py before the first attempt')
    if freeze.public_hashes(freeze.PUBLIC2 if fname == 'FREEZE-2.json' else None) != frozen['public']:
        sys.exit('the statements or the base scripts differ from %s: no attempt is run' % fname)
    pin = json.load(open(os.path.join(HERE, 'PIN.json')))
    local_commit = None              # a pod attempt does not need HOL on this Mac; the pod reports its own commit
    if not a.host:
        local_commit = subprocess.check_output(['git', '-C', HOLDIR, 'rev-parse', 'HEAD']).decode().strip()
        if local_commit != pin['hol_commit']:
            sys.exit('NOT JUDGED: HOL at %s is at %s, not the pinned %s (PIN.json)' % (HOLDIR, local_commit[:12], pin['hol_commit'][:12]))
    # the run's rules (RUN.json, when present): at most `cap` attempts per statement per family, none after it is judged
    runp = os.path.join(HERE, 'RUN.json')
    if os.path.exists(runp) and a.family in ('claude', 'gpt') and not a.lemma.startswith('C'):
        run = json.load(open(runp))
        prev = [json.loads(l) for l in open(LOG)] if os.path.exists(LOG) else []
        mine = [r for r in prev if r['lemma'] == a.lemma and r.get('family') == a.family and r.get('time_utc', '') >= run['start_utc']]
        if any(r['outcome'] in ('proved', 'refuted') for r in mine):
            sys.exit('NOT JUDGED: %s is already judged for family %s (%s); the run stops there' % (a.lemma, a.family, [r['outcome'] for r in mine if r['outcome'] in ('proved', 'refuted')][0]))
        if len(mine) >= run['cap']:
            sys.exit('NOT JUDGED: the cap of %d attempts at %s for family %s is reached' % (run['cap'], a.lemma, a.family))
    cpu_limit = a.cpu_limit or 2 * a.time_limit
    mem_kb = int(a.mem_limit_gb * 1048576)
    text = open(a.script, encoding='utf-8').read()
    waited = None
    if not a.host and not judgelib.text_check(text, skip_tokens=a.skip_text_check):
        # one local build at a time from this harness (held until the process exits), then no other HOL on the Mac
        global MACHINE_LOCK
        MACHINE_LOCK = open(os.path.join(HERE, '.mac-build.lock'), 'a'); fcntl.flock(MACHINE_LOCK, fcntl.LOCK_EX)
        waited = wait_for_free_mac(int(os.environ.get('ATTEMPT_WAIT_MAX', '7200')))
        if waited is None:
            sys.exit('NOT JUDGED: another HOL build kept this Mac busy for %s s; nothing was recorded, submit again'
                     % os.environ.get('ATTEMPT_WAIT_MAX', '7200'))
    n, work = reserve(a.family, a.lemma)
    shutil.copy(a.script, os.path.join(work, 'submitted.sml'))
    rec = dict(lemma=a.lemma, family=a.family, model=a.model, attempt=n, agent=a.agent,
               outcome=None, reason=None, wall_s=0.0, freeze=frozen['digest'], freeze_file=fname,
               script_sha256=hashlib.sha256(text.encode('utf-8')).hexdigest(),
               hol_commit=local_commit, mode='refute' if a.refute else 'prove',
               time_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), time_limit_s=a.time_limit,
               cpu_limit_s=cpu_limit, mem_limit_gb=a.mem_limit_gb, tokens=a.tokens,
               judge_code=judgelib.judge_code_digest(), host=None, isolation=None)
    if a.notes: rec['notes'] = a.notes
    if waited: rec['waited_for_mac_s'] = waited

    def finish(outcome, reason=None, res=None):
        rec['outcome'] = outcome; rec['reason'] = reason
        if res is not None:
            b = res['build']
            rec['wall_s'] = b['wall_s']; rec['cpu_s'] = b['cpu_s']; rec['peak_rss_mb'] = round(b['peak_group_rss_kb'] / 1024)
            if 'judge' in res: rec['judge'] = res['judge']
        out = append(rec)
        print(json.dumps(out))
        if res is not None and outcome in ('failed',):
            print('--- last lines of the build log ---\n' + ''.join(res['holmake_tail'].splitlines(True)[-60:]))
        sys.exit(0 if outcome in ('proved', 'refuted') else 1)

    reason = judgelib.text_check(text, skip_tokens=a.skip_text_check)
    if reason:
        rec['host'] = 'none (refused before the build)'
        finish('refused', reason)
    if a.host:
        sys.path.insert(0, os.path.join(HERE, 'pod'))
        import client
        rec['host'] = '%s:%s' % (a.host, a.port)
        res, info = client.run_remote(a.host, a.port, a.user, work, text, a.lemma, deps, a.family, n,
                                      a.time_limit, cpu_limit, mem_kb, mode=rec['mode'])
        rec['isolation'] = res.get('isolation')
        rec['hol_commit'] = info.get('hol_commit', rec['hol_commit'])
        rec['pod'] = info
        bad = client.check_pod(info, frozen)
        if bad:
            finish('refused', 'the pod is not at the frozen state: ' + bad, res)
    else:
        if a.isolation is None: sys.exit('no isolation for this platform: use --host (a Linux pod) or --isolation none')
        rec['host'] = 'local:mac'
        rec['isolation'] = a.isolation
        res = judgelib.build_and_judge(work, text, a.lemma, deps, BASE, HOLDIR, a.time_limit, cpu_limit, mem_kb, a.isolation,
                                       mode=rec['mode'])
    json.dump(res, open(os.path.join(work, 'result.json'), 'w'), indent=1)
    outcome, reason = judgelib.decide(res, a.lemma, a.time_limit, cpu_limit, mem_kb)
    finish(outcome, reason, res)


if __name__ == '__main__':
    main()
