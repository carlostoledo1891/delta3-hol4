(*
  delta3_check2 — Day 2 additions to the check: the inner certificate, strictness by
  strict diagonal dominance, and the cover.  delta3_checkScript.sml (Day 1) is unchanged.
  hol4/delta3 · cert-machine · Day 2 (2026-11-24)

  Inner certificate (CERT-FORMAT.md, "The inner file").  The asserted identity is

     L0(y) = y^T P y + SUM lam_ij y_i (1 - y_j) + SUM nu_j y_j (rin - m)
             + kap m (rin - m) + y^T N y + SUM c_i y_i

  inner_check rebuilds  L0 - (every multiplier term)  with the same accumulators as the
  slab check, requires its constant and its linear part to be exactly zero, forms the
  integer matrix 2 D P, and tests STRICT weighted diagonal dominance of
  4^T (2 D P) - 2 D Lw Lw^T  (every row: SUM_j d_j |G_ij| < 2 d_i G_ii).  Strict
  dominance gives positive definiteness directly; no leading minors, no Sylvester
  (the operator's decision of 2026-11-24; the JavaScript side uses leading minors,
  instruments/delta3/strict.js).  Every multiplier must be >= 0, N upper-triangular.

  L0 uses, per cut pair, the bound that vanishes at y = 0:  s_i s_j = +1 contributes
  nothing, s_i s_j = -1 contributes  - w_i w_j y_i y_j.

  Cover: the regions, in order, must reach from 0 to 1/2 without a gap.

  No soundness theorem is proved in this file.
*)
Theory delta3_check2
Ancestors
  arithmetic list integer cv_type cv_std delta3_check
Libs
  cv_transLib intLib

(* strict rows: SUM_j d_j |G_ij| - 2 d_i G_ii < 0 *)
Definition sdd_rows_def:
  sdd_rows (c1:int) (c2:int) (i:num) (M : int list list) (Lrows : int list list)
           (Lall : int list list) (ds : num list) (dall : num list) =
    case M of [] => T | (mrow :: Mr) =>
    case Lrows of [] => F | (li :: Lr) =>
    case ds of [] => F | (di :: dr) =>
      0 < di /\ rowsum c1 c2 i 0 li mrow Lall dall 0 < 0 /\
      sdd_rows c1 c2 (i + 1) Mr Lr Lall dr dall
End

Definition all_zero_def:
  all_zero [] = T /\
  all_zero ((x:int) :: xs) = (x = 0 /\ all_zero xs)
End

(* cut pairs of L0: s_i s_j = -1 gives - w_i w_j y_i y_j, s_i s_j = +1 gives nothing *)
Definition add_cut0_def:
  add_cut0 (D:num) (n:num) (U2:num) [] st = st /\
  add_cut0 D n U2 ((i:num, j:num, sg:int, ww:num, ain:num) :: rest) st =
    add_cut0 D n U2 rest
      (if sg = 1 then st
       else if sg = -1 then add_term D n 2 i j (-&ww) U2 st
       else bad st)
End

(* - lam y_i (1 - y_j),  lam = p/q >= 0 *)
Definition add_lam_def:
  add_lam (D:num) (n:num) [] st = st /\
  add_lam D n ((i:num, j:num, p:int, q:num) :: rest) st =
    if p < 0 then bad st else
      add_lam D n rest
        (add_term D n 2 i j p q (add_term D n 1 i 0 (-p) q st))
End

(* - nu_j y_j (rin - m),  nu_j = p/q >= 0, rin = rp/rq, m = mh / U *)
Definition add_nu_def:
  add_nu (D:num) (n:num) (U:num) (rp:int) (rq:num) (j:num) [] st = st /\
  add_nu D n U rp rq j ((p:int, q:num) :: rest) st =
    if p < 0 then bad st else
      add_nu D n U rp rq (j + 1) rest
        (add_term D n 4 j 0 p (q * U)
          (add_term D n 1 j 0 (-(p * rp)) (q * rq) st))
End

(* - kap m (rin - m) *)
Definition add_kap_def:
  add_kap (D:num) (n:num) (U:num) (rp:int) (rq:num) (kp:int) (kq:num) st =
    if kp < 0 then bad st else
      add_term D n 5 0 0 kp (kq * (U * U))
        (add_term D n 3 0 0 (-(kp * rp)) (kq * rq * U) st)
End

(* - y^T N y,  N given by its upper triangle (i <= j), entries p/q >= 0 *)
Definition add_nn_def:
  add_nn (D:num) (n:num) [] st = st /\
  add_nn D n ((i:num, j:num, p:int, q:num) :: rest) st =
    if p < 0 \/ j < i then bad st else
      add_nn D n rest
        (add_term D n 2 i j (-(if i = j then p else 2 * p)) q st)
End

(* - c_i y_i,  c_i = p/q >= 0 *)
Definition add_cc_def:
  add_cc (D:num) (n:num) (i:num) [] st = st /\
  add_cc D n i ((p:int, q:num) :: rest) st =
    if p < 0 then bad st else
      add_cc D n (i + 1) rest (add_term D n 1 i 0 (-p) q st)
End

Definition inner_poly_def:
  inner_poly (D:num) (n:num) ab cut full (rp:int) (rq:num) lam nu
             (kp:int) (kq:num) nn cc =
    add_cc D n 0 cc
      (add_nn D n nn
        (add_kap D n 1096 rp rq kp kq
          (add_nu D n 1096 rp rq 0 nu
            (add_lam D n lam
              (add_cut0 D n (1096 * 1096) cut
                (add_full D n (1096 * 1096) full
                  (add_cells D n 0 ab
                    (T, 0, REPLICATE n 0, REPLICATE n (REPLICATE n 0), 0,
                     REPLICATE n 0, 0))))))))
End

(* the integer matrix 2 D P: the quadratic block alone *)
Definition inner_matrix_def:
  inner_matrix (ws : int list)
               (st : bool # int # int list # int list list # int # int list # int) =
    case st of (ok, k, g, Cm, mL, mY, mM) =>
      tails (qrows mM 0 0 Cm (transp (LENGTH Cm) Cm) ws ws mY mY (lin mL ws g))
End

Definition inner_check_def:
  inner_check ab cut full (grid : num list) (rp:int) (rq:num) lam nu
              (kp:int) (kq:num) nn cc
              (D:num) (T2:num) (ds : num list) (Lw : int list list) =
    let n = LENGTH grid - 1 in
    let st = inner_poly D n ab cut full rp rq lam nu kp kq nn cc in
    let ws = widths grid in
      FST st /\ 0 < D /\ 0 < n /\
      (case grid of [] => F | (x :: xs) => x = 0) /\
      increasing grid /\ last_is 1096 grid /\
      LENGTH ab = n /\ LENGTH nu = n /\ LENGTH cc = n /\
      0 < rq /\ 0 < rp /\ rp <= &rq /\
      (case st of (ok, k, g, Cm, mL, mY, mM) =>
         k = 0 /\ all_zero (lin mL ws g)) /\
      LENGTH Lw = n /\ LENGTH ds = n /\
      sdd_rows (&(4 ** T2)) (&(2 * D)) 0 (inner_matrix ws st) Lw Lw ds ds
End

(* the cover: cover a ivs says every m with a < m <= 1/2 lies in one of ivs, when the
   intervals come in order; cover_all starts it at 0 *)
Definition cover_def:
  cover (ap:int) (aq:num) [] = (0 < aq /\ &aq <= 2 * ap) /\
  cover ap aq ((lp:int, lq:num, hp:int, hq:num) :: rest) =
    (0 < aq /\ 0 < lq /\ 0 < hq /\ lp * &aq <= ap * &lq /\
     (if ap * &hq < hp * &aq then cover hp hq rest else cover ap aq rest))
End

Definition cover_all_def:
  cover_all [] = F /\
  cover_all ((lp:int, lq:num, hp:int, hq:num) :: rest) =
    (0 < lq /\ 0 < hq /\ lp <= 0 /\ 0 <= hp /\ cover hp hq rest)
End

val _ = cv_trans sdd_rows_def;
val _ = cv_trans all_zero_def;
val _ = cv_trans add_cut0_def;
val _ = cv_trans add_lam_def;
val _ = cv_trans add_nu_def;
val _ = cv_trans add_kap_def;
val _ = cv_trans add_nn_def;
val _ = cv_trans add_cc_def;
val _ = cv_trans inner_poly_def;
val _ = cv_trans inner_matrix_def;
val _ = cv_trans inner_check_def;
val _ = cv_trans cover_def;
val _ = cv_trans cover_all_def;
