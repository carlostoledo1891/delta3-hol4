Theory attempt
Ancestors
  arithmetic delta3_stmts

val _ = let fun f () = f () in f () end;

Theorem C01:
  !n:num. n + 0 = n
Proof
  simp[]
QED
