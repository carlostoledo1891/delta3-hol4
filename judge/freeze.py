#!/usr/bin/env python3
"""freeze.py — fixes the benchmark's inputs before any attempt by either family.

  python3 freeze.py [--private <dir with key.json and lemma_source.py>]   writes FREEZE.json (refuses to overwrite)
  python3 freeze.py --check                                               compares the files with FREEZE.json

Public part (what attempt.py re-checks before every attempt): the statements theory, the dependency
table, the agent-facing list, and the three definition scripts, as they stand in harness/base and agents/.
Private part (hashes only; the files stay outside this folder): the truth key and its source.
The time is read from the system clock when the file is written.
"""
import hashlib, json, os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
PUBLIC = ['base/delta3_checkScript.sml', 'base/delta3_check2Script.sml', 'base/delta3_semScript.sml',
          'base/delta3_stmtsScript.sml', 'lemmas.json', '../agents/STATEMENTS.md', '../agents/BRIEF.md']
def sha(p): return hashlib.sha256(open(p, 'rb').read()).hexdigest()
# the re-keyed benchmark (FREEZE-2.json) also freezes the pitfalls note and the statement generator
PUBLIC2 = PUBLIC + ['../agents/PITFALLS.md', 'gen-statements.py']
def public_hashes(files=None): return {f: sha(os.path.join(HERE, f)) for f in (files or PUBLIC)}
if __name__ == '__main__':
    out = os.path.join(HERE, 'FREEZE.json')
    if '--check' in sys.argv:
        f2 = os.path.join(HERE, 'FREEZE-2.json')     # the re-keyed freeze (regen-key.sh) supersedes the first
        two = os.path.exists(f2)
        fr = json.load(open(f2 if two else out)); ok = public_hashes(PUBLIC2 if two else None) == fr['public']
        print('FREEZE ' + ('holds' if ok else 'BROKEN'), fr['digest'], fr['frozen_utc']); sys.exit(0 if ok else 1)
    if os.path.exists(out): sys.exit('FREEZE.json exists; a second freeze is a new benchmark and needs a new file name')
    pub = public_hashes(); priv = {}
    if '--private' in sys.argv:
        d = sys.argv[sys.argv.index('--private') + 1]
        priv = {f: sha(os.path.join(d, f)) for f in ('key.json', 'lemma_source.py', 'gen_lemmas.py')}
    digest = hashlib.sha256(json.dumps([pub, priv], sort_keys=True).encode()).hexdigest()
    json.dump(dict(frozen_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), digest=digest, public=pub, private_sha256=priv,
                   note='private_sha256: the truth key (which statements are planted, with counterexamples) and its source; '
                        'the files are kept outside this folder until the measurement is over'),
              open(out, 'w'), indent=1)
    print('frozen', digest)
