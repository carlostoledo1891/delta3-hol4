(*
  delta3_check — the slab-certificate check for delta_3 = 117/2192, as HOL4 functions
  that cv_transLib translates and cv_compute runs inside the kernel.
  hol4/delta3 · cert-machine · Day 1 (2026-11-24): the risk test only.

  Written from the mathematics (instruments/delta3/README.md, CERT-FORMAT.md and
  claimant/THEOREM-EXACT.md), not from verify.js line by line.

  What slab_check computes.  A slab certificate asserts the polynomial identity

      L_theta(y) - B - SUM_f mu_f f(y)  =  v^T S v,     v = (1, y_0 .. y_{n-1}),

  with S + eps I positive semidefinite.  slab_check
    1. rebuilds p = L_theta - B - SUM mu_f f as exact coefficients (constant, linear,
       quadratic, and three accumulators for the terms in m = SUM w_k y_k), refusing a
       negative multiplier, a theta outside [0,1], an index out of range, an unknown
       form kind, a triangle form with a repeated index or s1 s2 s3 <> 1;
    2. forms the integer matrix M = 2 D (S + eps I), D a common denominator;
    3. takes an UNTRUSTED integer factor Lw, a scale 2^T and positive weights d, and
       tests that G = 4^T M - 2 D Lw Lw^T satisfies, in every row i,
             SUM_j d_j |G_ij|  <=  2 d_i G_ii       (the sum includes j = i)
       that is, d_i G_ii >= SUM_{j<>i} d_j |G_ij| and G_ii >= 0: weighted diagonal
       dominance with a non-negative diagonal;
    4. tests eps >= 0, 0 <= lo < hi <= 1, B - eps (1+n) > 0 and claim <= B - eps (1+n).

  Number representation.  A rational is a pair (p:int, q:num) read as p/q, exactly as
  the certificate file writes it.  Nothing is normalised.  Every coefficient enters the
  accumulators as the INTEGER  p * (D DIV q), and the check refuses unless q divides D
  (D MOD q = 0), so that integer is exactly D * (p/q).  The common denominator D is a
  hint supplied with the witness; a wrong D can only cause a refusal.

  What is DATA here and not yet derived in HOL4 (plan, Days 2-3, step 1): the model
  constants of the grid — per cell (a_i, b_i), the full pairs with s_i s_j W_i W_j, the
  cut pairs with s_i s_j, W_i W_j and 4 U^2 A_in.  On Day 1 they are exported from the
  JavaScript verifier's own gridData.

  No soundness theorem is proved in this file.  "slab_check ... = T" says the function
  returns true on the data; it does not yet say that the bound holds.
*)
Theory delta3_check
Ancestors
  arithmetic list integer cv_type cv_std
Libs
  cv_transLib intLib

(* ---- the scaled value of p/q at the common denominator D ------------------- *)

Definition sc_def:
  sc (D:num) (p:int) (q:num) = p * &(D DIV q)
End

(* ---- accumulators: add v at position n of a list / at (i, j) of a matrix ---- *)

Definition addl_def:
  addl (n:num) (v:int) [] = [] /\
  addl n v (x::xs) = if n = 0 then (x + v) :: xs else x :: addl (n - 1) v xs
End

Definition addm_def:
  addm (i:num) (j:num) (v:int) [] = [] /\
  addm i j v (r::rs) = if i = 0 then addl j v r :: rs else r :: addm (i - 1) j v rs
End

(* the state: (ok, k, g, Cm, mL, mY, mM) stands for the polynomial
     ( k + SUM g_i y_i + SUM C_ij y_i y_j + mL mh + SUM mY_i mh y_i + mM mh^2 ) / D,
   mh = SUM W_k y_k = U m, valid while ok holds *)

Definition bad_def:
  bad (st : bool # int # int list # int list list # int # int list # int) =
    case st of (ok, k, g, Cm, mL, mY, mM) => (F, k, g, Cm, mL, mY, mM)
End

(* tag 0: 1    1: y_i    2: y_i y_j    3: mh    4: mh y_i    5: mh^2 *)
Definition add_term_def:
  add_term (D:num) (n:num) (tag:num) (i:num) (j:num) (p:int) (q:num)
           (st : bool # int # int list # int list list # int # int list # int) =
    case st of (ok, k, g, Cm, mL, mY, mM) =>
      let v = sc D p q in
      let ok1 = (ok /\ D MOD q = 0 /\ i < n /\ j < n) in
        if tag = 0 then (ok1, k + v, g, Cm, mL, mY, mM)
        else if tag = 1 then (ok1, k, addl i v g, Cm, mL, mY, mM)
        else if tag = 2 then (ok1, k, g, addm i j v Cm, mL, mY, mM)
        else if tag = 3 then (ok1, k, g, Cm, mL + v, mY, mM)
        else if tag = 4 then (ok1, k, g, Cm, mL, addl i v mY, mM)
        else if tag = 5 then (ok1, k, g, Cm, mL, mY, mM + v)
        else (F, k, g, Cm, mL, mY, mM)
End

(* ---- L_theta ---------------------------------------------------------------- *)

(* per cell: a_i y_i + b_i y_i^2 (the bathtub minorant) *)
Definition add_cells_def:
  add_cells (D:num) (n:num) (i:num) [] st = st /\
  add_cells D n i ((ap:int, aq:num, bp:int, bq:num) :: rest) st =
    add_cells D n (i + 1) rest
      (add_term D n 2 i i bp bq (add_term D n 1 i 0 ap aq st))
End

(* per full pair: s_i s_j w_i w_j y_i y_j, with c = s_i s_j W_i W_j and w = W / U *)
Definition add_full_def:
  add_full (D:num) (n:num) (U2:num) [] st = st /\
  add_full D n U2 ((i:num, j:num, c:int) :: rest) st =
    add_full D n U2 rest (add_term D n 2 i j c U2 st)
End

(* per cut pair, theta = tp/tq, ww = W_i W_j, ain = 4 U^2 A_in, 4 U^2 A_out = 4 ww - ain:
     s_i s_j = +1 :  (1 - theta) (w_i w_j y_i y_j - A_out)
     s_i s_j = -1 :  theta (- A_in) + (1 - theta) (- w_i w_j y_i y_j)            *)
Definition add_cut_def:
  add_cut (D:num) (n:num) (U2:num) [] st = st /\
  add_cut D n U2 (((i:num, j:num, sg:int, ww:num, ain:num), (tp:int, tq:num)) :: rest) st =
    if tp < 0 \/ &tq < tp then bad st else
      let om = &tq - tp in
        add_cut D n U2 rest
          (if sg = 1 then
             add_term D n 0 0 0 (-(om * (4 * &ww - &ain))) (tq * (4 * U2))
               (add_term D n 2 i j (om * &ww) (tq * U2) st)
           else if sg = -1 then
             add_term D n 0 0 0 (-(tp * &ain)) (tq * (4 * U2))
               (add_term D n 2 i j (-(om * &ww)) (tq * U2) st)
           else bad st)
End

(* ---- the forms: each call adds  - mu * f(y),  mu = mp/mq >= 0 ---------------- *)

(* - c/q * z_a z_b,  z = 1 - 2 y :   - c + 2c y_a + 2c y_b - 4c y_a y_b *)
Definition add_zz_def:
  add_zz (D:num) (n:num) (c:int) (q:num) (a:num) (b:num) st =
    add_term D n 2 a b (-(4 * c)) q
      (add_term D n 1 b 0 (2 * c) q
        (add_term D n 1 a 0 (2 * c) q
          (add_term D n 0 0 0 (-c) q st)))
End

Definition add_form_def:
  add_form (D:num) (n:num) (U:num) (lp:int) (lq:num) (hp:int) (hq:num)
           (kind:num) (i:num) (j:num) (k:num) (s1:int) (s2:int) (s3:int)
           (mp:int) (mq:num) st =
    if mp < 0 then bad st
    (* yy: y_i y_j *)
    else if kind = 0 then add_term D n 2 i j (-mp) mq st
    (* 11: (1 - y_i)(1 - y_j) = 1 - y_i - y_j + y_i y_j *)
    else if kind = 1 then
      add_term D n 2 i j (-mp) mq
        (add_term D n 1 j 0 mp mq
          (add_term D n 1 i 0 mp mq
            (add_term D n 0 0 0 (-mp) mq st)))
    (* y1: y_i (1 - y_j) *)
    else if kind = 2 then
      add_term D n 2 i j mp mq (add_term D n 1 i 0 (-mp) mq st)
    (* yd: y_i - y_i^2 *)
    else if kind = 3 then
      add_term D n 2 i i mp mq (add_term D n 1 i 0 (-mp) mq st)
    (* 11d: (1 - y_i)^2 *)
    else if kind = 4 then
      add_term D n 2 i i (-mp) mq
        (add_term D n 1 i 0 (2 * mp) mq
          (add_term D n 0 0 0 (-mp) mq st))
    (* y: y_i *)
    else if kind = 5 then add_term D n 1 i 0 (-mp) mq st
    (* 1: 1 - y_i *)
    else if kind = 6 then
      add_term D n 1 i 0 mp mq (add_term D n 0 0 0 (-mp) mq st)
    (* mlo: m - lo = mh / U - lp / lq *)
    else if kind = 7 then
      add_term D n 0 0 0 (mp * lp) (mq * lq)
        (add_term D n 3 0 0 (-mp) (mq * U) st)
    (* mhi: hi - m *)
    else if kind = 8 then
      add_term D n 3 0 0 mp (mq * U)
        (add_term D n 0 0 0 (-(mp * hp)) (mq * hq) st)
    (* mm: (m - lo)(hi - m) = - m^2 + (lo + hi) m - lo hi *)
    else if kind = 9 then
      add_term D n 0 0 0 (mp * lp * hp) (mq * lq * hq)
        (add_term D n 3 0 0 (-(mp * hp)) (mq * hq * U)
          (add_term D n 3 0 0 (-(mp * lp)) (mq * lq * U)
            (add_term D n 5 0 0 mp (mq * (U * U)) st)))
    (* mlo_y: (m - lo) y_i *)
    else if kind = 10 then
      add_term D n 1 i 0 (mp * lp) (mq * lq)
        (add_term D n 4 i 0 (-mp) (mq * U) st)
    (* mlo_1: (m - lo)(1 - y_i) = m - lo - m y_i + lo y_i *)
    else if kind = 11 then
      add_term D n 1 i 0 (-(mp * lp)) (mq * lq)
        (add_term D n 4 i 0 mp (mq * U)
          (add_term D n 0 0 0 (mp * lp) (mq * lq)
            (add_term D n 3 0 0 (-mp) (mq * U) st)))
    (* mhi_y: (hi - m) y_i *)
    else if kind = 12 then
      add_term D n 4 i 0 mp (mq * U)
        (add_term D n 1 i 0 (-(mp * hp)) (mq * hq) st)
    (* mhi_1: (hi - m)(1 - y_i) = hi - hi y_i - m + m y_i *)
    else if kind = 13 then
      add_term D n 4 i 0 (-mp) (mq * U)
        (add_term D n 3 0 0 mp (mq * U)
          (add_term D n 1 i 0 (mp * hp) (mq * hq)
            (add_term D n 0 0 0 (-(mp * hp)) (mq * hq) st)))
    (* tri: 1 + s1 z_i z_j + s2 z_j z_k + s3 z_i z_k, three distinct indices,
       every s = +-1 and s1 s2 s3 = +1 *)
    else if kind = 14 then
      if i = j \/ j = k \/ i = k \/
         ~(s1 = 1 \/ s1 = -1) \/ ~(s2 = 1 \/ s2 = -1) \/ ~(s3 = 1 \/ s3 = -1) \/
         ~(s1 * s2 * s3 = 1)
      then bad st
      else
        add_zz D n (s3 * mp) mq i k
          (add_zz D n (s2 * mp) mq j k
            (add_zz D n (s1 * mp) mq i j
              (add_term D n 0 0 0 (-mp) mq st)))
    else bad st
End

Definition add_forms_def:
  add_forms (D:num) (n:num) (U:num) (lp:int) (lq:num) (hp:int) (hq:num) [] st = st /\
  add_forms D n U lp lq hp hq
    ((kind:num, i:num, j:num, k:num, s1:int, s2:int, s3:int, mp:int, mq:num) :: rest) st =
    add_forms D n U lp lq hp hq rest
      (add_form D n U lp lq hp hq kind i j k s1 s2 s3 mp mq st)
End

(* ---- the grid: W_i = grid[i+1] - grid[i], strictly increasing from 0 to U ---- *)

Definition widths_def:
  widths [] = ([] : int list) /\
  widths ((x:num) :: xs) =
    case xs of [] => [] | (y :: ys) => (&y - &x) :: widths xs
End

Definition increasing_def:
  increasing [] = T /\
  increasing ((x:num) :: xs) =
    case xs of [] => T | (y :: ys) => x < y /\ increasing xs
End

Definition last_is_def:
  last_is (u:num) [] = F /\
  last_is u (x :: xs) = case xs of [] => (x = u) | (y :: ys) => last_is u xs
End

(* ---- the matrix M = 2 D (S + eps I) ------------------------------------------ *)

Definition heads_def:
  heads [] = ([] : int list) /\
  heads (r :: rs) = (case r of [] => 0 | (x :: xs) => x) :: heads rs
End

Definition tails_def:
  tails [] = ([] : int list list) /\
  tails (r :: rs) = (case r of [] => [] | (x :: xs) => xs) :: tails rs
End

Definition transp_def:
  transp (n:num) (m : int list list) =
    if n = 0 then [] else heads m :: transp (n - 1) (tails m)
End

(* g_i + c W_i *)
Definition lin_def:
  lin (c:int) [] (xs : int list) = ([] : int list) /\
  lin c ((w:int) :: ws) xs =
    case xs of [] => [] | (x :: xt) => (x + c * w) :: lin c ws xt
End

(* row i of  Cm + Cm^T + W mY^T + mY W^T + 2 mM W W^T + 2 e I *)
Definition qrow_def:
  qrow (wi:int) (myi:int) (mwi:int) (e2:int) (i:num) (j:num)
       (crow : int list) (ctrow : int list) (ws : int list) (mys : int list) =
    case crow of [] => [] | (c :: cr) =>
    case ctrow of [] => [] | (ct :: ctr) =>
    case ws of [] => [] | (w :: wr) =>
    case mys of [] => [] | (my :: myr) =>
      (c + ct + wi * my + w * myi + mwi * w + (if i = j then e2 else 0))
        :: qrow wi myi mwi e2 i (j + 1) cr ctr wr myr
End

Definition qrows_def:
  qrows (mM:int) (e2:int) (i:num) (Cm : int list list) (Ct : int list list)
        (wall : int list) (ws : int list) (myall : int list) (mys : int list)
        (g : int list) =
    case Cm of [] => [] | (crow :: Cr) =>
    case Ct of [] => [] | (ctrow :: Ctr) =>
    case ws of [] => [] | (wi :: wr) =>
    case mys of [] => [] | (myi :: myr) =>
    case g of [] => [] | (gi :: gr) =>
      (gi :: qrow wi myi (2 * mM * wi) e2 i 0 crow ctrow wall myall)
        :: qrows mM e2 (i + 1) Cr Ctr wall wr myall myr gr
End

(* ---- weighted diagonal dominance of G = c1 M - c2 Lw Lw^T -------------------- *)

Definition dot_def:
  dot (acc:int) [] (ys : int list) = acc /\
  dot acc ((x:int) :: xs) ys =
    case ys of [] => acc | (y :: yt) => dot (acc + x * y) xs yt
End

(* SUM_j d_j |G_ij|  -  2 d_i G_ii   for row i, as one integer: the row passes when it
   is <= 0 (with d_i > 0 this also forces G_ii >= 0) *)
Definition rowsum_def:
  rowsum (c1:int) (c2:int) (i:num) (j:num) (li : int list) (mrow : int list)
         (Ls : int list list) (ds : num list) (acc:int) =
    case mrow of [] => acc | (m :: mr) =>
    case Ls of [] => acc | (lj :: Lr) =>
    case ds of [] => acc | (d :: dr) =>
      let gij = c1 * m - c2 * dot 0 li lj in
        rowsum c1 c2 i (j + 1) li mr Lr dr
               (acc + &d * (if gij < 0 then -gij else gij)
                    - (if i = j then 2 * &d * gij else 0))
End

Definition dd_rows_def:
  dd_rows (c1:int) (c2:int) (i:num) (M : int list list) (Lrows : int list list)
          (Lall : int list list) (ds : num list) (dall : num list) =
    case M of [] => T | (mrow :: Mr) =>
    case Lrows of [] => F | (li :: Lr) =>
    case ds of [] => F | (di :: dr) =>
      0 < di /\ rowsum c1 c2 i 0 li mrow Lall dall 0 <= 0 /\
      dd_rows c1 c2 (i + 1) Mr Lr Lall dr dall
End

(* ---- the matrix and the whole check ------------------------------------------ *)

Definition slab_matrix_def:
  slab_matrix (D:num) (ep:int) (eq:num) (ws : int list)
              (st : bool # int # int list # int list list # int # int list # int) =
    case st of (ok, k, g, Cm, mL, mY, mM) =>
      let e2 = 2 * sc D ep eq in
      let g1 = lin mL ws g in
        ((2 * k + e2) :: g1) ::
          qrows mM e2 0 Cm (transp (LENGTH Cm) Cm) ws ws mY mY g1
End

Definition slab_poly_def:
  slab_poly (D:num) (n:num) ab cut full (Bp:int) (Bq:num)
            (lp:int) (lq:num) (hp:int) (hq:num) theta forms =
    add_forms D n 1096 lp lq hp hq forms
      (add_term D n 0 0 0 (-Bp) Bq
        (add_cut D n (1096 * 1096) (ZIP (cut, theta))
          (add_full D n (1096 * 1096) full
            (add_cells D n 0 ab
              (T, 0, REPLICATE n 0, REPLICATE n (REPLICATE n 0), 0,
               REPLICATE n 0, 0)))))
End

Definition slab_check_def:
  slab_check ab cut full (grid : num list)
             (lp:int) (lq:num) (hp:int) (hq:num) (Bp:int) (Bq:num)
             (ep:int) (eq:num) (cp:int) (cq:num) theta forms
             (D:num) (T2:num) (ds : num list) (Lw : int list list) =
    let n = LENGTH grid - 1 in
    let st = slab_poly D n ab cut full Bp Bq lp lq hp hq theta forms in
    let M = slab_matrix D ep eq (widths grid) st in
    let bnd = Bp * &eq - ep * &(n + 1) * &Bq in
      FST st /\ 0 < D /\ D MOD eq = 0 /\ 0 < n /\
      (case grid of [] => F | (x :: xs) => x = 0) /\
      increasing grid /\ last_is 1096 grid /\
      LENGTH ab = n /\ LENGTH cut = LENGTH theta /\
      0 <= ep /\ 0 < lq /\ 0 < hq /\ 0 <= lp /\ lp * &hq < hp * &lq /\ hp <= &hq /\
      0 < cq /\ 0 < bnd /\ cp * &Bq * &eq <= bnd * &cq /\
      LENGTH Lw = n + 1 /\ LENGTH ds = n + 1 /\
      dd_rows (&(4 ** T2)) (&(2 * D)) 0 M Lw Lw ds ds
End

(* ---- translation to the cv type ---------------------------------------------- *)

val _ = cv_trans sc_def;
val _ = cv_trans addl_def;
val _ = cv_trans addm_def;
val _ = cv_trans bad_def;
val _ = cv_trans add_term_def;
val _ = cv_trans add_cells_def;
val _ = cv_trans add_full_def;
val _ = cv_trans add_cut_def;
val _ = cv_trans add_zz_def;
val _ = cv_trans add_form_def;
val _ = cv_trans add_forms_def;
val _ = cv_trans widths_def;
val _ = cv_trans increasing_def;
val _ = cv_trans last_is_def;
val _ = cv_trans heads_def;
val _ = cv_trans tails_def;
val _ = cv_trans transp_def;
val _ = cv_trans lin_def;
val _ = cv_trans qrow_def;
val _ = cv_trans qrows_def;
val _ = cv_trans dot_def;
val _ = cv_trans rowsum_def;
val _ = cv_trans dd_rows_def;
val _ = cv_trans slab_matrix_def;
val _ = cv_trans slab_poly_def;
val _ = cv_trans slab_check_def;

(* ---- two lemmas the data loader's conversion uses: from_int on a literal ------ *)

Theorem from_int_pos:
  from_int (&n) = cv$Num n
Proof
  simp [from_int_def]
QED

Theorem from_int_neg:
  from_int (-&n) = if n = 0 then cv$Num 0 else cv$Pair (cv$Num n) (cv$Num 0)
Proof
  rw [from_int_def]
QED
