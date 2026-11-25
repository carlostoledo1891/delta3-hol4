(*
  delta3_sem — what the check is ABOUT: real-valued meanings for the things the integer
  functions of delta3_check and delta3_check2 compute.  Definitions only; the soundness
  statements are in delta3_stmtsScript.sml and are stated in these terms.
  hol4/delta3 · cert-machine · Day 2 (2026-11-24)

  Everything is finite-dimensional.  y is a real list of length n (the cell averages),
  m = (SUM W_k y_k) / 1096.  L_theta and L0 are the polynomials of CERT-FORMAT.md built
  from the model constants (ab, cut, full).  That those constants are areas and bathtub
  constants of phi*, and that E(sigma) >= L(y), is analysis and is not stated here.
*)
Theory delta3_sem
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2
Libs
  intLib realLib

(* the rational p/q as a real *)
Definition qv_def:
  qv (p:int) (q:num) = real_of_int p / &q
End

(* SUM_i g_i y_i *)
Definition ldot_def:
  ldot [] (y : real list) = 0r /\
  ldot ((g:int) :: gs) y =
    case y of [] => 0 | (x :: xs) => real_of_int g * x + ldot gs xs
End

(* SUM_i u_i (SUM_j C_ij y_j) *)
Definition qform_def:
  qform [] (u : real list) (y : real list) = 0r /\
  qform ((r : int list) :: rs) u y =
    case u of [] => 0 | (x :: xs) => x * ldot r y + qform rs xs y
End

Definition sumsq_def:
  sumsq [] = 0r /\
  sumsq ((x:real) :: xs) = x * x + sumsq xs
End

(* the polynomial an accumulator state stands for, times D *)
Definition st_val_def:
  st_val (ws : int list)
         (st : bool # int # int list # int list list # int # int list # int)
         (y : real list) =
    case st of (ok, k, g, Cm, mL, mY, mM) =>
      real_of_int k + ldot g y + qform Cm y y + real_of_int mL * ldot ws y +
      ldot mY y * ldot ws y + real_of_int mM * (ldot ws y * ldot ws y)
End

Definition st_wf_def:
  st_wf (n:num)
        (st : bool # int # int list # int list list # int # int list # int) <=>
    case st of (ok, k, g, Cm, mL, mY, mM) =>
      LENGTH g = n /\ LENGTH Cm = n /\ EVERY (\r. LENGTH r = n) Cm /\ LENGTH mY = n
End

Definition st0_def:
  st0 (n:num) =
    (T, 0:int, REPLICATE n (0:int), REPLICATE n (REPLICATE n (0:int)), 0:int,
     REPLICATE n (0:int), 0:int)
End

(* the monomial of an add_term tag *)
Definition mono_def:
  mono (ws : int list) (tag:num) (i:num) (j:num) (y : real list) =
    if tag = 0 then 1r
    else if tag = 1 then EL i y
    else if tag = 2 then EL i y * EL j y
    else if tag = 3 then ldot ws y
    else if tag = 4 then ldot ws y * EL i y
    else ldot ws y * ldot ws y
End

Definition in_box_def:
  in_box (n:num) (y : real list) <=>
    LENGTH y = n /\ EVERY (\x. 0 <= x /\ x <= 1) y
End

Definition mval_def:
  mval (grid : num list) (y : real list) = ldot (widths grid) y / 1096
End

(* ---- L_theta and L0, from the model constants -------------------------------- *)

Definition cells_val_def:
  cells_val (i:num) [] (y : real list) = 0r /\
  cells_val i ((ap:int, aq:num, bp:int, bq:num) :: rest) y =
    qv ap aq * EL i y + qv bp bq * (EL i y * EL i y) + cells_val (i + 1) rest y
End

Definition full_val_def:
  full_val [] (y : real list) = 0r /\
  full_val ((i:num, j:num, c:int) :: rest) y =
    qv c (1096 * 1096) * (EL i y * EL j y) + full_val rest y
End

Definition cut_val_def:
  cut_val [] (y : real list) = 0r /\
  cut_val (((i:num, j:num, sg:int, ww:num, ain:num), (tp:int, tq:num)) :: rest) y =
    (if sg = 1 then
       (1 - qv tp tq) *
       (&ww / &(1096 * 1096) * (EL i y * EL j y) -
        (&ww / &(1096 * 1096) - &ain / &(4 * (1096 * 1096))))
     else
       qv tp tq * -(&ain / &(4 * (1096 * 1096))) +
       (1 - qv tp tq) * -(&ww / &(1096 * 1096) * (EL i y * EL j y)))
    + cut_val rest y
End

Definition Ltheta_def:
  Ltheta ab cut full theta (y : real list) =
    cells_val 0 ab y + full_val full y + cut_val (ZIP (cut, theta)) y
End

Definition cut0_val_def:
  cut0_val [] (y : real list) = 0r /\
  cut0_val ((i:num, j:num, sg:int, ww:num, ain:num) :: rest) y =
    (if sg = 1 then 0 else -(&ww / &(1096 * 1096) * (EL i y * EL j y)))
    + cut0_val rest y
End

Definition L0_def:
  L0 ab cut full (y : real list) =
    cells_val 0 ab y + full_val full y + cut0_val cut y
End

(* ---- the forms of a slab certificate ----------------------------------------- *)

Definition form_val_def:
  form_val (m:real) (lo:real) (hi:real) (kind:num) (i:num) (j:num) (k:num)
           (s1:int) (s2:int) (s3:int) (y : real list) =
    if kind = 0 then EL i y * EL j y
    else if kind = 1 then (1 - EL i y) * (1 - EL j y)
    else if kind = 2 then EL i y * (1 - EL j y)
    else if kind = 3 then EL i y - EL i y * EL i y
    else if kind = 4 then (1 - EL i y) * (1 - EL i y)
    else if kind = 5 then EL i y
    else if kind = 6 then 1 - EL i y
    else if kind = 7 then m - lo
    else if kind = 8 then hi - m
    else if kind = 9 then (m - lo) * (hi - m)
    else if kind = 10 then (m - lo) * EL i y
    else if kind = 11 then (m - lo) * (1 - EL i y)
    else if kind = 12 then (hi - m) * EL i y
    else if kind = 13 then (hi - m) * (1 - EL i y)
    else
      1 + real_of_int s1 * ((1 - 2 * EL i y) * (1 - 2 * EL j y))
        + real_of_int s2 * ((1 - 2 * EL j y) * (1 - 2 * EL k y))
        + real_of_int s3 * ((1 - 2 * EL i y) * (1 - 2 * EL k y))
End

(* which indices a form kind reads *)
Definition form_idx_ok_def:
  form_idx_ok (n:num) (kind:num) (i:num) (j:num) (k:num) <=>
    (kind <= 2 ==> i < n /\ j < n) /\
    ((3 <= kind /\ kind <= 6) \/ (10 <= kind /\ kind <= 13) ==> i < n) /\
    (kind = 14 ==> i < n /\ j < n /\ k < n)
End

Definition forms_val_def:
  forms_val (m:real) (lo:real) (hi:real) [] (y : real list) = 0r /\
  forms_val m lo hi
    ((kind:num, i:num, j:num, k:num, s1:int, s2:int, s3:int, mp:int, mq:num) :: rest) y =
    qv mp mq * form_val m lo hi kind i j k s1 s2 s3 y + forms_val m lo hi rest y
End

(* ---- the multiplier terms of the inner certificate --------------------------- *)

Definition lam_val_def:
  lam_val [] (y : real list) = 0r /\
  lam_val ((i:num, j:num, p:int, q:num) :: rest) y =
    qv p q * (EL i y * (1 - EL j y)) + lam_val rest y
End

Definition nu_val_def:
  nu_val (m:real) (rin:real) (j:num) [] (y : real list) = 0r /\
  nu_val m rin j ((p:int, q:num) :: rest) y =
    qv p q * (EL j y * (rin - m)) + nu_val m rin (j + 1) rest y
End

Definition nn_val_def:
  nn_val [] (y : real list) = 0r /\
  nn_val ((i:num, j:num, p:int, q:num) :: rest) y =
    (if i = j then 1 else 2) * qv p q * (EL i y * EL j y) + nn_val rest y
End

Definition cc_val_def:
  cc_val (i:num) [] (y : real list) = 0r /\
  cc_val i ((p:int, q:num) :: rest) y = qv p q * EL i y + cc_val (i + 1) rest y
End

Definition mults_val_def:
  mults_val (m:real) (rin:real) lam nu (kap:real) nn cc (y : real list) =
    lam_val lam y + nu_val m rin 0 nu y + kap * (m * (rin - m)) + nn_val nn y +
    cc_val 0 cc y
End

(* ---- the cover ---------------------------------------------------------------- *)

Definition in_some_def:
  in_some (m:real) [] = F /\
  in_some m ((lp:int, lq:num, hp:int, hq:num) :: rest) =
    ((qv lp lq <= m /\ m <= qv hp hq) \/ in_some m rest)
End
