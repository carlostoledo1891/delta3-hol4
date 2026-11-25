#!/usr/bin/env python3
"""rebuild-accepted.py — every ACCEPTED attempt (outcome proved or refuted) rebuilt in a FRESH, separate process
from its submitted script alone, against the frozen base, and judged again.  hol4/delta3/harness · 2026-11-25

  python3 rebuild-accepted.py --all            every accepted line of attempts.jsonl not rebuilt yet
  python3 rebuild-accepted.py --seq 26 [...]   the given lines (again, if already rebuilt)
  [--include-controls]                         also the harness's own controls (C01, C02)

For each one it makes ONE folder, accepted/<seq>-<family>-<id>-<n>/ — the interface for the independent replay
(OpenTheory export + an independent checker, built by another agent):
  script.sml        the script exactly as submitted (sha256 in INTERFACE.json)
  INTERFACE.json    statement id, theorem name (<id> or <id>_refuted), theory name (attempt), mode, the dependency
                    constants (proofs: deps ==> statement; refutations: ~statement), the base folder and its digest,
                    the freeze digest, the HOL commit, the original attempts.jsonl line, the verdict
  rebuild/          the fresh build (Holmakefile, .hol/objs/attemptTheory.*, holmake.log, judge.sml, judge.out)
  theory/           a copy of the rebuilt theory files (what the replay reads)
  rebuild.json      the judge's facts on the rebuild and its decision
Verdict REBUILT when the rebuild's decision equals the original outcome and the script is byte-identical;
MISMATCH otherwise. One line per rebuild in accepted/REBUILDS.tsv. Nothing is written to attempts.jsonl.
On this Mac it runs under sandbox.sb, one at a time, waiting while any other HOL build runs (as attempt.py).
A rebuilt proof still counts only after a person has read it (RUN-PROTOCOL.md, the reader's checklist).
"""
import os, sys, json, time, shutil, argparse, hashlib, platform, fcntl
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import judgelib
import attempt as A


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--all', action='store_true'); ap.add_argument('--seq', type=int, nargs='*', default=[])
    ap.add_argument('--include-controls', action='store_true')
    ap.add_argument('--host'); ap.add_argument('--port', default='22'); ap.add_argument('--user', default='root')
    a = ap.parse_args()
    recs = [json.loads(l) for l in open(A.LOG)]
    acc = [r for r in recs if r['outcome'] in ('proved', 'refuted') and (a.include_controls or not r['lemma'].startswith('C'))]
    out_root = os.path.join(HERE, 'accepted'); os.makedirs(out_root, exist_ok=True)
    tsv = os.path.join(out_root, 'REBUILDS.tsv')
    done = set(l.split('\t')[1] for l in open(tsv)) if os.path.exists(tsv) else set()
    todo = [r for r in acc if (r['seq'] in a.seq) or (a.all and str(r['seq']) not in done)]
    lemmas = json.load(open(os.path.join(HERE, 'lemmas.json')))
    for r in todo:
        src_dir = os.path.join(HERE, 'work', r['family'], '%s-%d' % (r['lemma'], r['attempt']))
        src = os.path.join(src_dir, 'submitted.sml')
        if not os.path.exists(src):
            src = os.path.join(src_dir, 'attemptScript.sml')
        text = open(src, encoding='utf-8').read()
        sha = hashlib.sha256(text.encode('utf-8')).hexdigest()
        folder = os.path.join(out_root, '%d-%s-%s-%d' % (r['seq'], r['family'], r['lemma'], r['attempt']))
        shutil.rmtree(folder, ignore_errors=True); os.makedirs(os.path.join(folder, 'rebuild'))
        open(os.path.join(folder, 'script.sml'), 'w', encoding='utf-8').write(text)
        mode = r.get('mode', 'prove')
        deps = lemmas[r['lemma']]['deps'] if r['lemma'] in lemmas else []
        tl, cl, mk = r.get('time_limit_s', 600), r.get('cpu_limit_s') or 2 * r.get('time_limit_s', 600), int(r.get('mem_limit_gb', 6) * 1048576)
        where = 'local:mac'
        if a.host:      # on the pod: a fresh job, a fresh directory, a fresh process, same judge
            sys.path.insert(0, os.path.join(HERE, 'pod')); import client
            res, info = client.run_remote(a.host, a.port, a.user, os.path.join(folder, 'rebuild'), text, r['lemma'], deps,
                                          'rebuild', r['seq'], tl, cl, mk, mode=mode)
            frozen = A.freeze_file()[1]
            bad = client.check_pod(info, frozen)
            if bad:
                raise SystemExit('the pod is not at the frozen state: ' + bad)
            where = '%s:%s' % (a.host, a.port)
            objs = os.path.join(folder, 'rebuild', 'theory')
        else:
            lock = open(os.path.join(HERE, '.mac-build.lock'), 'a'); fcntl.flock(lock, fcntl.LOCK_EX)
            A.wait_for_free_mac(7200)
            res = judgelib.build_and_judge(os.path.join(folder, 'rebuild'), text, r['lemma'], deps, A.BASE, A.HOLDIR, tl, cl, mk,
                                           'mac' if platform.system() == 'Darwin' else 'none', mode=mode)
            fcntl.flock(lock, fcntl.LOCK_UN); lock.close()
            objs = os.path.join(folder, 'rebuild', '.hol', 'objs')
        outcome, reason = judgelib.decide(res, r['lemma'], tl, cl, mk)
        os.makedirs(os.path.join(folder, 'theory'))
        for f in (sorted(os.listdir(objs)) if os.path.isdir(objs) else []):
            if f.startswith('attemptTheory'):
                shutil.copy(os.path.join(objs, f), os.path.join(folder, 'theory', f))
        json.dump(dict(res, decision=outcome, reason=reason), open(os.path.join(folder, 'rebuild.json'), 'w'), indent=1)
        verdict = 'REBUILT' if (outcome == r['outcome'] and sha == r['script_sha256']) else 'MISMATCH'
        json.dump(dict(seq=r['seq'], statement=r['lemma'], theory='attempt', mode=mode,
                       theorem=r['lemma'] if mode == 'prove' else r['lemma'] + '_refuted',
                       goal_rule=('deps ==> rhs of %s_def' % r['lemma']) if mode == 'prove' else ('~(rhs of %s_def)' % r['lemma']),
                       deps=deps, statements_theory='delta3_stmts', base=A.BASE, base_digest=res['base_before'],
                       freeze=r.get('freeze'), hol_commit=r.get('hol_commit'), script_sha256=sha, rebuild_verdict=verdict,
                       rebuild_decision=outcome, rebuilt_on=where, rebuilt_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), original=r),
                  open(os.path.join(folder, 'INTERFACE.json'), 'w'), indent=1)
        new = not os.path.exists(tsv)
        with open(tsv, 'a') as f:
            if new:
                f.write('time_utc\tseq\tfamily\tstatement\tattempt\toriginal\trebuild\tverdict\twall_s\tfolder\n')
            f.write('\t'.join([time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), str(r['seq']), r['family'], r['lemma'], str(r['attempt']),
                               r['outcome'], outcome, verdict, str(res['build']['wall_s']), os.path.basename(folder)]) + '\n')
        print('%s seq %d %s %s: original %s, rebuild %s' % (verdict, r['seq'], r['family'], r['lemma'], r['outcome'], outcome))


if __name__ == '__main__':
    main()
