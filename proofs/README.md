# proofs/

- `SOURCES.tsv`: the 42 lemmas of the three chains, one proof each, where it comes from and how blind it is.
- `accepted/`: proofs accepted by the judge during the blind run. 40 of them are on the chain.
  Two are kept only as the run's record and are NOT on the chain: `245-claude-S040-1` (L26) and `422-claude-S046-1`
  (L29). They were the run's only accepted proofs of those lemmas, and both were built on an earlier proof written by
  an agent that had read the answer key (CONTAMINATED in both blinding audits).
- `cleanroom/`: L26 and L29 proved again after scoring by a fresh agent that never saw any earlier proof of them,
  each accepted at its first attempt by a copy of the frozen judge (records in `records/cleanroom/`). These are on the
  chain in place of the two above.
- `builder/`: L28 (S149), which neither family proved; finished after scoring by the agent that had read the key.
- `assembly/`: the theories that join the lemmas into the three soundness theorems and the Layer-1 theorem, and the
  read-back (`check.sml`). `tools/acc_rename.py` turns each proof into `acc_<statement>Script.sml` by renaming its
  `Theory attempt` line, and checks both hashes against `SOURCES.tsv`.
