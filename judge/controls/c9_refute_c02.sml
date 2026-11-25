Theory attempt
Ancestors
  arithmetic delta3_stmts

(* refutation control: C02 is false on purpose ((n:num) + 1 = n); a correct refutation -> refuted *)
Theorem C02_neg[local]:
  ~C02
Proof
  simp[C02_def]
QED

Theorem C02_refuted = CONV_RULE (RAND_CONV (REWR_CONV C02_def)) C02_neg
