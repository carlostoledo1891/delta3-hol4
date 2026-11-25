#!/usr/bin/env python3
"""judgelib.py — the build-and-judge step of the soundness-lemma benchmark, in ONE place.
hol4/delta3/harness · written 2026-11-24 after the freeze of 22:03:28Z (JUDGE.json records it).

Used by attempt.py on the Mac (isolation "mac": macOS sandbox-exec with sandbox.sb) and by
pod/runner.py on a Linux pod (isolation "linux": pod/jail, a seccomp + Landlock wrapper, run as an
unprivileged slot user). The outcome is decided by decide() and nowhere else.

What one attempt is (build_and_judge):
  1. the script is copied into a FRESH directory; a Holmakefile there points at the base theories;
  2. Holmake builds attemptTheory under the isolation, with three limits — wall time, CPU time per
     process (RLIMIT_CPU) and resident memory of the whole process group (sampled every 0.5 s,
     the group killed when the sum passes the limit);
  3. a separate HOL process (the judge), under the same isolation and limits, loads the saved theory
     and writes its facts (EXACT, HYPS, ORACLES, AXIOMS, THEORY_AXIOMS) to judge.out;
  4. the base theories are hashed before and after.

What the isolation does NOT do: the attempt's ML code runs in the processes that write
attemptTheory.dat and judge.out. HOL4 trusts its own disk format (Thm.disk_thm makes a theorem of
whatever a .dat file says) and an ML program can print anything. So a DELIBERATE forgery from inside
the build is stopped only by the text check below (a deny-list of identifiers, a filter, not a proof)
and by reading every proved script. See JUDGE.json "not_covered".
"""
import os, re, sys, json, time, signal, hashlib, subprocess, resource, platform, shutil

HERE = os.path.dirname(os.path.abspath(__file__))

# ---- 1. the text check ------------------------------------------------------------------------
# Checked on the RAW text (comments included: a comment that says "cheat" is refused too).
# The first line is the Day-2 list (kept as it was); the rest was added with the sandbox: identifiers
# that give file, process, network or FFI access, or that make a theorem without a proof, matched as
# whole identifiers so that `open Thm` + `disk_thm` or `structure T = TextIO` are caught too.
DENY_RAW = [r'\bcheat\b', r'\bCHEAT', r'mk_thm', r'mk_oracle_thm', r'new_axiom', r'mk_axiom', r'\bTag\.', r'add_tag',
            r'unsafeCast', r'RunCall', r'\bUnsafe\b', r'OS\.Process', r'OS\.FileSys', r'Posix\.', r'TextIO\.open',
            r'BinIO\.', r'\buse\s*"', r'new_theory', r'export_theory', r'PolyML\.', r'Thm\.disk_thm', r'DISK_THM',
            # added 2026-11-24 with the sandbox
            r'\bdisk_thm\b', r'\bmk_disk_thm\b', r'\bmk_axiom_thm\b', r'\bThm\b', r'\bTheory\s*\.', r'\bTheoryReader\b',
            r'\bSharingTables\b', r'\bThyDataSexp\b', r'\bHOLsexp\b', r'\badjoin_to_theory\b', r'\badjoin_after_completion\b',
            r'\bTextIO\b', r'\bBinIO\b', r'\bTextPrimIO\b', r'\bBinPrimIO\b', r'\bImperativeIO\b', r'\bStreamIO\b',
            r'\bPrimIO\b', r'\bPosix\b', r'\bUnix\b', r'\bPolyML\b', r'\bForeign\b', r'\bSysteml\b', r'\bHOLFileSys\b',
            r'\bPortable\b', r'\bSocket\b', r'\bINetSock\b', r'\bUnixSock\b', r'\bGenericSock\b', r'\bNetHostDB\b',
            r'\bloadPath\b', r'\bquse\b', r'\bQUse\b']
# Checked on the text with SML comments removed (these are also ordinary English words).
DENY_CODE = [r'\buse\b', r'\bload\b', r'\bsystem\b', r'\bOS\b', r'\bMeta\b', r'\bTag\b', r'\bopen_out\b',
             r'\bopen_append\b', r'\bopen_in\b']


def strip_comments(text):
    """SML text with (* ... *) comments (nested) replaced by a space; string literals kept.
    Raises ValueError on an unterminated comment or string, which the caller refuses."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        if depth == 0 and text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            if j >= n:
                raise ValueError('unterminated string literal')
            out.append(text[i:j + 1]); i = j + 1
        elif text.startswith('(*', i):
            depth += 1; i += 2
        elif depth > 0 and text.startswith('*)', i):
            depth -= 1; i += 2
            if depth == 0:
                out.append(' ')
        else:
            if depth == 0:
                out.append(text[i])
            i += 1
    if depth:
        raise ValueError('unterminated comment')
    return ''.join(out)


def text_check(text, skip_tokens=False):
    """None when the script may be built, else the reason it is refused."""
    first = re.search(r'^Theory attempt(\[[a-z_,]*\])?\s*$', text, re.M)
    if not first:
        return 'the script has no line "Theory attempt"'
    if skip_tokens:
        return None
    for pat in DENY_RAW:
        m = re.search(pat, text)
        if m:
            return 'forbidden token in the script: ' + m.group(0)
    try:
        code = strip_comments(text)
    except ValueError as e:
        return 'the script cannot be read for the token check: ' + str(e)
    for pat in DENY_CODE:
        m = re.search(pat, code)
        if m:
            return 'forbidden identifier in the script (outside comments): ' + m.group(0)
    return None


# ---- 2. hashing --------------------------------------------------------------------------------
def sha256_file(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


def tree_digest(base):
    """sha256 over the base theories' source and object files (locks and logs excluded)."""
    h = hashlib.sha256()
    for root, dirs, files in os.walk(base):
        dirs.sort()
        for f in sorted(files):
            if f.endswith(('.dat', '.sml', '.sig', '.uo', '.ui')) and '.hol/locks' not in root and '.hol/logs' not in root:
                h.update(f.encode()); h.update(open(os.path.join(root, f), 'rb').read())
    return h.hexdigest()


JUDGE_FILES = ['judgelib.py', 'attempt.py', 'attempt.sh', 'sandbox.sb', 'PIN.json', 'pod/runner.py', 'pod/jail.c', 'pod/client.py']


def judge_code_digest():
    """one sha256 over the judge's own files, as they stand (recorded in every attempt)."""
    h = hashlib.sha256()
    for f in JUDGE_FILES:
        p = os.path.join(HERE, f)
        if os.path.exists(p):
            h.update(f.encode()); h.update(open(p, 'rb').read())
    return h.hexdigest()


# ---- 3. running a command under limits ----------------------------------------------------------
def _group_rss_kb(pgid):
    """resident memory, in kB, summed over every process whose process group is pgid"""
    try:
        out = subprocess.run(['ps', '-A', '-o', 'pgid=,rss='], capture_output=True, text=True, timeout=10).stdout
    except Exception:
        return 0
    tot = 0
    for line in out.splitlines():
        parts = line.split()
        if len(parts) == 2 and parts[0] == str(pgid):
            try:
                tot += int(parts[1])
            except ValueError:
                pass
    return tot


def run_limited(cmd, cwd, env, time_s, cpu_s, mem_kb, log, stdin_path=None, preexec_extra=None):
    """Runs cmd in its own session (so its process group is its pid). Returns a dict:
       rc (None when killed), wall_s, cpu_s (user+sys of the command and its waited-for children),
       max_rss_kb (largest single process), peak_group_rss_kb (sampled sum), killed (None|time|memory|cpu)."""
    def pre():
        os.setsid()
        resource.setrlimit(resource.RLIMIT_CPU, (cpu_s, cpu_s + 10))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        if preexec_extra:
            preexec_extra()
    t0 = time.time()
    fin = open(stdin_path) if stdin_path else subprocess.DEVNULL
    with open(log, 'w') as out:
        p = subprocess.Popen(cmd, cwd=cwd, env=env, stdin=fin, stdout=out, stderr=subprocess.STDOUT, preexec_fn=pre)
    killed, peak, last_sample, status, ru = None, 0, 0.0, None, None
    while True:
        pid, st, r = os.wait4(p.pid, os.WNOHANG)
        if pid == p.pid:
            status, ru = st, r
            break
        now = time.time()
        if now - t0 > time_s:
            killed = 'time'
        elif now - last_sample >= 0.5:
            last_sample = now
            rss = _group_rss_kb(p.pid)
            peak = max(peak, rss)
            if rss > mem_kb:
                killed = 'memory'
        if killed:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            pid, status, ru = os.wait4(p.pid, 0)
            break
        time.sleep(0.1)
    # whatever is left in the group (a child that outlived its parent) is killed too
    try:
        os.killpg(p.pid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass
    p.returncode = os.waitstatus_to_exitcode(status) if hasattr(os, 'waitstatus_to_exitcode') else status
    if stdin_path:
        fin.close()
    cpu = ru.ru_utime + ru.ru_stime
    maxrss = ru.ru_maxrss // 1024 if platform.system() == 'Darwin' else ru.ru_maxrss
    sig = -p.returncode if p.returncode is not None and p.returncode < 0 else None
    if killed is None and sig in (signal.SIGXCPU, signal.SIGKILL) and cpu >= 0.95 * cpu_s:
        killed = 'cpu'
    return dict(rc=None if killed else p.returncode, wall_s=round(time.time() - t0, 2), cpu_s=round(cpu, 2),
                max_rss_kb=maxrss, peak_group_rss_kb=max(peak, maxrss), killed=killed)


# ---- 4. isolation wrappers -----------------------------------------------------------------------
def poly_prefix():
    p = shutil.which('poly')
    return os.path.dirname(os.path.dirname(os.path.realpath(p))) if p else '/opt/homebrew'


def mac_wrap(work, holdir):
    sb = os.path.join(HERE, 'sandbox.sb')
    return ['sandbox-exec', '-f', sb, '-D', 'BUILD=' + os.path.realpath(work), '-D', 'HOLDIR=' + os.path.realpath(holdir),
            '-D', 'POLY=' + poly_prefix()]


def judge_script(base, lemma, deps, mode='prove'):
    """mode prove: the theorem named <lemma> must be  deps ==> statement;
       mode refute: the theorem named <lemma>_refuted must be  ~statement  (the statement alone, closed)."""
    depl = ', '.join('c "%s"' % d for d in deps)
    name = lemma if mode == 'prove' else lemma + '_refuted'
    return r'''
loadPath := "%(base)s/.hol/objs" :: "%(base)s" :: ".hol/objs" :: !loadPath;
load "delta3_stmtsTheory"; load "attemptTheory";
val out = TextIO.openOut "judge.out";
fun say s = (TextIO.output (out, s ^ "\n"); TextIO.flushOut out);
val _ = (let
  val th = DB.fetch "attempt" "%(name)s"
  fun c s = prim_mk_const {Thy = "delta3_stmts", Name = s}
  val stmt = rhs (concl (DB.fetch "delta3_stmts" "%(id)s_def"))
  val deps = [%(deps)s]
  val goal = %(goal)s
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in say ("EXACT " ^ Bool.toString (aconv (concl th) goal));
     say ("HYPS " ^ Int.toString (length (hyp th)));
     say ("ORACLES " ^ String.concatWith "," oracles);
     say ("AXIOMS " ^ String.concatWith "," axioms);
     say ("THEORY_AXIOMS " ^ Int.toString (length (DB.axioms "attempt")))
  end handle e => say ("JUDGE_ERROR " ^ General.exnMessage e));
val _ = TextIO.closeOut out;
''' % dict(base=base, id=lemma, deps=depl, name=name,
                goal='mk_neg stmt' if mode == 'refute' else 'if null deps then stmt else mk_imp (list_mk_conj deps, stmt)')


def tail(path, n):
    try:
        return ''.join(open(path, errors='replace').readlines()[-n:])
    except OSError:
        return ''


def build_and_judge(work, script_text, lemma, deps, base, holdir, time_s, cpu_s, mem_kb, isolation,
                    wrap=None, preexec_extra=None, judge_time_s=300, mode='prove'):
    """work must be a fresh, empty directory. Returns the raw facts; decide() reads them."""
    if isolation == 'mac':
        wrap = mac_wrap(work, holdir)
    elif isolation == 'none':
        wrap = []
    elif wrap is None:
        raise ValueError('isolation %s needs a wrapper' % isolation)
    open(os.path.join(work, 'attemptScript.sml'), 'w', encoding='utf-8').write(script_text)
    open(os.path.join(work, 'Holmakefile'), 'w').write('INCLUDES = %s\n' % base)
    os.makedirs(os.path.join(work, 'tmp'), exist_ok=True)
    env = dict(os.environ, PATH=os.path.join(holdir, 'bin') + ':' + os.environ.get('PATH', '/usr/bin:/bin'),
               TMPDIR=os.path.join(work, 'tmp'), HOME=work)
    for k in ('SSH_AUTH_SOCK', 'JUDGE_SSH_KEY'):
        env.pop(k, None)
    res = dict(isolation=isolation, mode=mode, base_before=tree_digest(base))
    res['build'] = run_limited(wrap + ['nice', '-n', '10', 'Holmake', 'attemptTheory.uo'], work, env, time_s, cpu_s, mem_kb,
                               os.path.join(work, 'holmake.log'), preexec_extra=preexec_extra)
    res['holmake_tail'] = tail(os.path.join(work, 'holmake.log'), 200)
    if res['build']['rc'] == 0:
        jp = os.path.join(work, 'judge.sml')
        open(jp, 'w').write(judge_script(base, lemma, deps, mode))
        res['judge_run'] = run_limited(wrap + ['nice', '-n', '10', 'hol'], work, env, judge_time_s, 2 * judge_time_s, mem_kb,
                                       os.path.join(work, 'judge.log'), stdin_path=jp, preexec_extra=preexec_extra)
        jo = os.path.join(work, 'judge.out')
        facts = {}
        if os.path.exists(jo):
            for l in open(jo, errors='replace'):
                l = l.rstrip('\n')
                k, _, v = l.partition(' ')
                facts[k] = v
        res['judge'] = facts
    res['base_after'] = tree_digest(base)
    return res


# ---- 5. the decision (the only place an outcome is decided) -------------------------------------
def decide(res, lemma, time_s, cpu_s, mem_kb):
    """proved | refuted | failed | timeout | refused, and the reason"""
    b = res['build']
    mode = res.get('mode', 'prove')
    name = lemma if mode == 'prove' else lemma + '_refuted'
    if b['killed'] == 'time':
        return 'timeout', 'Holmake did not finish in %d s' % time_s
    if b['killed'] == 'cpu':
        return 'timeout', 'a process used its CPU limit of %d s' % cpu_s
    if b['killed'] == 'memory':
        return 'failed', 'memory limit: the attempt\'s processes held more than %.1f GB resident' % (mem_kb / 1048576)
    if b['rc'] != 0:
        return 'failed', 'Holmake exit %s' % b['rc']
    if res['base_after'] != res['base_before']:
        return 'refused', 'the base theories changed during the attempt'
    jr = res.get('judge_run') or {}
    if jr.get('killed'):
        return 'refused', 'the judge did not finish (%s limit)' % jr['killed']
    facts = res.get('judge') or {}
    if 'JUDGE_ERROR' in facts or 'EXACT' not in facts:
        return 'refused', 'no theorem named %s could be judged: %s' % (name, facts.get('JUDGE_ERROR', 'the judge produced no verdict'))
    if facts['EXACT'] != 'true':
        return 'refused', 'the theorem named %s does not have the recorded %s' % (name, 'statement' if mode == 'prove' else 'negated statement')
    if facts.get('HYPS') != '0':
        return 'refused', 'the theorem has hypotheses'
    bad = [o for o in facts.get('ORACLES', '').split(',') if o and o != 'DISK_THM']
    if bad:
        return 'refused', 'oracle tag: ' + ','.join(bad)
    if facts.get('AXIOMS'):
        return 'refused', 'axiom tag: ' + facts['AXIOMS']
    if facts.get('THEORY_AXIOMS') != '0':
        return 'refused', 'the attempt theory declares an axiom'
    return ('proved' if mode == 'prove' else 'refuted'), None
