# The answer key

These are the files that said, during the blind run, which statements were true and which were planted false. They
were encrypted with a passphrase only I held, before the run began, and decrypted only after both model families had
finished and the scoring program had been sealed. They are published here so that anyone can check the scores.

**How to check that this is the key the run used.** Before the run, the judge wrote `judge/FREEZE-2.json`
(2026-11-25 10:25:58 UTC; the run started at 11:02:30 UTC). It records the sha256 of every file here, under
`plaintext_sha256`, and a digest over those hashes that every judged attempt in `agents/attempts.jsonl` carries.
From the repository root:

```
python3 tools/check-key.py        # each file's sha256 against FREEZE-2.json, the digest, and the attempts' digest
sha256sum -c SHA256SUMS           # (in this folder) the same hashes, as the key's own list
```

What is in it: `key.json` (each statement's role, its truth, the lemma it comes from, its "May use" list, and for a
planted one the counterexample), `LEMMAS.md` (the 42 true lemmas and how they depend on each other), the planted
variants and their kernel checks (`delta3_plantedScript.sml`, `planted-*.tsv`), and the generator (`gen_lemmas.py`,
`lemma_source.py`, `keep.json`, `planted-map.json`). `key-freeze1.json` is the key of the first freeze, which was
replaced before the run because it had leaked into agent transcripts on my disk.
