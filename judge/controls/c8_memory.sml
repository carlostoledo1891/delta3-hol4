Theory attempt
Ancestors
  arithmetic delta3_stmts

(* limit control: a script that keeps allocating; run with a low --mem-limit-gb, it must be killed
   by the judge's memory watchdog (outcome failed, reason "memory limit"). *)
fun grow acc k = if k = 0 then acc else grow (Array.array (1048576, k) :: acc) (k - 1);
val big = grow [] 100000;
val _ = print (Int.toString (length big) ^ "\n");

Theorem C01:
  !n:num. n + 0 = n
Proof
  simp[]
QED
