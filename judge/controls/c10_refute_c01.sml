Theory attempt
Ancestors
  arithmetic delta3_stmts

(* refutation control: C01 is TRUE; a "refutation" cannot be built -> failed, never refuted *)
Theorem C01_neg[local]:
  ~C01
Proof
  simp[C01_def]
QED

Theorem C01_refuted = CONV_RULE (RAND_CONV (REWR_CONV C01_def)) C01_neg
