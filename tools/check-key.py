#!/usr/bin/env python3
"""tools/check-key.py — checks the published answer key (agents/key/) against the freeze that was written BEFORE
the blind run (judge/FREEZE-2.json, 2026-11-25T10:25:58Z; the run started at 11:02:30Z).

  1. every file of agents/key/ that FREEZE-2.json names has exactly the sha256 recorded there ("plaintext_sha256");
  2. FREEZE-2.json's digest is what its own fields give: sha256 of json.dumps([public, plaintext_sha256,
     archive_sha256], sort_keys=True) — so the key's hashes cannot have been changed after the freeze without
     changing the digest;
  3. every judged attempt in agents/attempts.jsonl carries that same digest ("freeze").
Exit 0 only if all three hold.  Usage: python3 tools/check-key.py   (from the repository root)"""
import hashlib, json, os, sys
R = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
fr = json.load(open(os.path.join(R, 'judge', 'FREEZE-2.json')))
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
ok = True
for name, want in sorted(fr['plaintext_sha256'].items()):
    got = sha(os.path.join(R, 'agents', 'key', name))
    print('%s  %s  %s' % ('OK  ' if got == want else 'DIFF', want[:16], name)); ok &= got == want
dig = hashlib.sha256(json.dumps([fr['public'], fr['plaintext_sha256'], fr['archive_sha256']], sort_keys=True).encode()).hexdigest()
print('%s  FREEZE-2 digest %s (frozen %s)' % ('OK  ' if dig == fr['digest'] else 'DIFF', dig[:16], fr['frozen_utc'])); ok &= dig == fr['digest']
runs = [json.loads(l) for l in open(os.path.join(R, 'agents', 'attempts.jsonl'))]
judged = [r for r in runs if r.get('freeze_file') == 'FREEZE-2.json' and r.get('outcome') in ('proved', 'refuted')]
same = all(r['freeze'] == fr['digest'] for r in judged)
print('%s  %d judged attempts under FREEZE-2 carry that digest' % ('OK  ' if same else 'DIFF', len(judged))); ok &= same
print('key: ' + ('CHECKED' if ok else 'DOES NOT MATCH THE FREEZE')); sys.exit(0 if ok else 1)
