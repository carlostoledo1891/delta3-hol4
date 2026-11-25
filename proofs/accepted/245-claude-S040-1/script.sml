(* S040 — weighted diagonal dominance of G = c1 M - c2 Lw Lw^T makes the quadratic form of M
   non-negative.  Agent claude-b3 (model claude-opus-5-5), 2026-11-25; the proof of the Day-2 S33 attempt 9, for the same statement.
   Route: lists -> index functions over count n (real_sigma's sum); the core is the
   unweighted lemma "sum_j |H i j| <= 2 H i i for every row ==> z^T H z >= 0" (dd_core),
   applied to H i j = d i * G i j * d j and z i = x i / d i; the Gram part is a sum of squares.
   Linearity steps over lambdas go through simp (higher-order matching); everything else is
   instantiated explicitly (rewrite_tac matches first-order only). *)
Theory attempt
Ancestors
  arithmetic list integer real intreal real_sigma pred_set delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib


(* REAL_ARITH eliminates abs (and conditionals) everywhere, also inside a sum's lambda, and does not
   come back from that.  So every maximal sum/dsum application outside binders is generalised to a
   variable first (real_sigma's sum is the constant Sum). *)
fun sum_atoms t =
  if is_comb t then
    let val (c, args) = strip_comb t in
      if is_const c andalso mem (fst (dest_const c)) ["Sum", "sum", "dsum"] andalso length args = 2 then [t]
      else sum_atoms (rator t) @ sum_atoms (rand t)
    end
  else [];
fun GEN_SUMS_TAC (g as (_, w)) =
  MAP_EVERY (fn t => SPEC_TAC (t, genvar (type_of t))) (op_mk_set aconv (sum_atoms w)) g;
val SUM_ARITH_TAC = GEN_SUMS_TAC >> REAL_ARITH_TAC;

(* ================= 1. sums over count n ================= *)

Theorem csum_last[local]:
  !n (f:num -> real). sum (count (SUC n)) f = f n + sum (count n) f
Proof
  rpt gen_tac >> rewrite_tac[COUNT_SUC] >>
  simp_tac (srw_ss()) [SUM_CLAUSES, FINITE_COUNT]
QED

Theorem csum_head[local]:
  !n (f:num -> real). sum (count (SUC n)) f = f 0 + sum (count n) (\i. f (SUC i))
Proof
  Induct
  >- rewrite_tac[csum_last, COUNT_ZERO, CONJUNCT1 SUM_CLAUSES]
  >> gen_tac >> once_rewrite_tac[csum_last] >> BETA_TAC
  >> first_x_assum (qspec_then `f` SUBST1_TAC) >> SUM_ARITH_TAC
QED

Theorem sum_sub3[local]:
  !n (a:num -> real) b c. sum (count n) (\x. a x - b x - c x) = sum (count n) a - sum (count n) b - sum (count n) c
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [SUM_SUB', FINITE_COUNT]
QED

Definition dsum_def:
  dsum (n:num) (f:num -> num -> real) = sum (count n) (\i. sum (count n) (\j. f i j))
End

Theorem dsum_le[local]:
  !n f g. (!i j. i < n /\ j < n ==> f i j <= g i j) ==> dsum n f <= dsum n g
Proof
  rpt strip_tac >> rewrite_tac[dsum_def] >>
  irule SUM_LE' >> simp_tac (srw_ss()) [FINITE_COUNT] >> rpt strip_tac >>
  irule SUM_LE' >> simp_tac (srw_ss()) [FINITE_COUNT] >> rpt strip_tac >>
  first_x_assum irule >> asm_rewrite_tac[]
QED

Theorem dsum_eq[local]:
  !n f g. (!i j. i < n /\ j < n ==> f i j = g i j) ==> dsum n f = dsum n g
Proof
  rpt strip_tac >> rewrite_tac[dsum_def] >>
  irule SUM_EQ' >> simp_tac (srw_ss()) [] >> rpt strip_tac >>
  irule SUM_EQ' >> simp_tac (srw_ss()) [] >> rpt strip_tac >>
  first_x_assum irule >> asm_rewrite_tac[]
QED

Theorem dsum_sub[local]:
  !n f g. dsum n (\i j. f i j - g i j) = dsum n f - dsum n g
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [dsum_def, SUM_SUB', FINITE_COUNT]
QED

Theorem dsum_sub3[local]:
  !n a b c. dsum n (\i j. a i j - b i j - c i j) = dsum n a - dsum n b - dsum n c
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [dsum_def, SUM_SUB', FINITE_COUNT]
QED

Theorem dsum_cmul[local]:
  !n c f. dsum n (\i j. c * f i j) = c * dsum n f
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [dsum_def, SUM_LMUL]
QED

Theorem dsum_swap[local]:
  !n f. dsum n (\i j. f j i) = dsum n f
Proof
  rpt gen_tac >> rewrite_tac[dsum_def] >> BETA_TAC >>
  qspecl_then [`\i j. f j i`, `n`, `n`] mp_tac SUM_SWAP_COUNT >> BETA_TAC >>
  disch_then ACCEPT_TAC
QED

Theorem dsum_delta[local]:
  !n (c:num -> real). dsum n (\i j. if j = i then c i else 0) = sum (count n) c
Proof
  rpt gen_tac >> rewrite_tac[dsum_def] >> BETA_TAC >>
  irule SUM_EQ' >> rpt strip_tac >> BETA_TAC >>
  rewrite_tac[SUM_DELTA] >> asm_rewrite_tac[]
QED

Theorem dsum_rmul_row[local]:
  !n f (c:num -> real). dsum n (\i j. f i j * c i) = sum (count n) (\i. sum (count n) (\j. f i j) * c i)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [dsum_def, SUM_RMUL]
QED

(* ================= 2. the core: unweighted diagonal dominance ================= *)

Theorem pw_diag[local]:
  !a h:real. 2 * h * (a * a) - abs h * (a * a / 2) - abs h * (a * a / 2) <= a * h * a
Proof
  rpt gen_tac >> `0 <= a * a` by rewrite_tac[REAL_LE_SQUARE] >>
  Cases_on `0 <= h`
  >- (`abs h = h` by asm_rewrite_tac[ABS_REFL] >> pop_assum SUBST1_TAC >> SUM_ARITH_TAC)
  >> `abs h = -h` by (pop_assum mp_tac >> SUM_ARITH_TAC) >> pop_assum SUBST1_TAC >>
  `0 <= -h * (a * a)` by (irule REAL_LE_MUL >> asm_rewrite_tac[] >> pop_assum mp_tac >> SUM_ARITH_TAC) >>
  pop_assum mp_tac >> SUM_ARITH_TAC
QED

Theorem pw_off[local]:
  !a b h:real. 0 - abs h * (a * a / 2) - abs h * (b * b / 2) <= a * h * b
Proof
  rpt gen_tac >> Cases_on `0 <= h`
  >- (`abs h = h` by asm_rewrite_tac[ABS_REFL] >> pop_assum SUBST1_TAC >>
      `0 <= h * ((a + b) * (a + b))` by (irule REAL_LE_MUL >> asm_rewrite_tac[REAL_LE_SQUARE]) >>
      pop_assum mp_tac >> SUM_ARITH_TAC)
  >> `abs h = -h` by (pop_assum mp_tac >> SUM_ARITH_TAC) >> pop_assum SUBST1_TAC >>
  `0 <= -h * ((a - b) * (a - b))` by
     (irule REAL_LE_MUL >> rewrite_tac[REAL_LE_SQUARE] >> pop_assum mp_tac >> SUM_ARITH_TAC) >>
  pop_assum mp_tac >> SUM_ARITH_TAC
QED

Theorem dd_core[local]:
  !n (H:num -> num -> real) (z:num -> real).
    (!i j. i < n /\ j < n ==> H i j = H j i) /\
    (!i. i < n ==> sum (count n) (\j. abs (H i j)) <= 2 * H i i) ==>
    0 <= dsum n (\i j. z i * H i j * z j)
Proof
  rpt strip_tac >>
  `dsum n (\i j. (if j = i then 2 * H i i * (z i * z i) else 0) - abs (H i j) * (z i * z i / 2)
                  - abs (H i j) * (z j * z j / 2)) <= dsum n (\i j. z i * H i j * z j)`
     by (irule dsum_le >> rpt strip_tac >> BETA_TAC >> Cases_on `j = i`
         >- (pop_assum SUBST_ALL_TAC >> rewrite_tac[pw_diag])
         >> qpat_x_assum `~(j = i)` (fn th => rewrite_tac[th, pw_off])) >>
  qspecl_then [`n`, `\i j. if j = i then 2 * H i i * (z i * z i) else 0`, `\i j. abs (H i j) * (z i * z i / 2)`,
               `\i j. abs (H i j) * (z j * z j / 2)`] (assume_tac o BETA_RULE) dsum_sub3 >>
  qspecl_then [`n`, `\i. 2 * H i i * (z i * z i)`] (assume_tac o BETA_RULE) dsum_delta >>
  qspecl_then [`n`, `\i j. abs (H i j)`, `\i. z i * z i / 2`] (assume_tac o BETA_RULE) dsum_rmul_row >>
  `dsum n (\i j. abs (H i j) * (z j * z j / 2)) = dsum n (\i j. abs (H i j) * (z i * z i / 2))` by
     (qspecl_then [`n`, `\i j. abs (H i j) * (z j * z j / 2)`] (SUBST1_TAC o SYM o BETA_RULE) dsum_swap >>
      irule dsum_eq >> rpt strip_tac >> BETA_TAC >>
      `H j i = H i j` by (qpat_x_assum `!i j. i < n /\ j < n ==> H i j = H j i` irule >> asm_rewrite_tac[]) >>
      pop_assum SUBST1_TAC >> REFL_TAC) >>
  qspecl_then [`n`, `\i. 2 * H i i * (z i * z i)`, `\i. sum (count n) (\j. abs (H i j)) * (z i * z i / 2)`,
               `\i. sum (count n) (\j. abs (H i j)) * (z i * z i / 2)`] (assume_tac o BETA_RULE) sum_sub3 >>
  `0 <= sum (count n) (\x. 2 * H x x * (z x * z x) - sum (count n) (\j. abs (H x j)) * (z x * z x / 2)
                          - sum (count n) (\j. abs (H x j)) * (z x * z x / 2))` by
     (irule SUM_POS_LE >> rewrite_tac[FINITE_COUNT] >> rpt strip_tac >> BETA_TAC >>
      `x < n` by (pop_assum mp_tac >> rewrite_tac[IN_COUNT]) >>
      `sum (count n) (\j. abs (H x j)) <= 2 * H x x` by
         (qpat_x_assum `!i. i < n ==> _` irule >> first_assum ACCEPT_TAC) >>
      `0 <= (z x * z x) * (2 * H x x - sum (count n) (\j. abs (H x j)))` by
         (irule REAL_LE_MUL >> rewrite_tac[REAL_LE_SQUARE] >> pop_assum mp_tac >> SUM_ARITH_TAC) >>
      pop_assum mp_tac >> SUM_ARITH_TAC) >>
  rpt (qpat_x_assum `_ = _` mp_tac) >> rpt (qpat_x_assum `_ <= _` mp_tac) >> SUM_ARITH_TAC
QED

(* ================= 3. the weighted form ================= *)

Theorem div_cancel[local] = RealField.REAL_FIELD
  ``!a b g x y:real. a <> 0 /\ b <> 0 ==> x / a * (a * g * b) * (y / b) = x * g * y``

Theorem wdd_psd[local]:
  !n (G:num -> num -> real) (d:num -> real) (x:num -> real).
    (!i j. i < n /\ j < n ==> G i j = G j i) /\ (!i. i < n ==> 0 < d i) /\
    (!i. i < n ==> sum (count n) (\j. d j * abs (G i j)) <= 2 * d i * G i i) ==>
    0 <= dsum n (\i j. x i * G i j * x j)
Proof
  rpt strip_tac >>
  qspecl_then [`n`, `\i j. d i * G i j * d j`, `\i. x i / d i`] mp_tac dd_core >> BETA_TAC >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >>
          `G i j = G j i` by (qpat_x_assum `!i j. i < n /\ j < n ==> G i j = G j i` irule >> asm_rewrite_tac[]) >>
          pop_assum SUBST1_TAC >> SUM_ARITH_TAC)
      >> rpt strip_tac >>
      `!j. j < n ==> abs (d i * G i j * d j) = d i * (d j * abs (G i j))` by
         (rpt strip_tac >> rewrite_tac[ABS_MUL] >>
          `abs (d i) = d i /\ abs (d j) = d j` by
             (rewrite_tac[ABS_REFL] >> conj_tac >> irule REAL_LT_IMP_LE >>
              qpat_x_assum `!i. i < n ==> 0 < d i` irule >> asm_rewrite_tac[]) >>
          asm_rewrite_tac[] >> SUM_ARITH_TAC) >>
      `sum (count n) (\j. abs (d i * G i j * d j)) = d i * sum (count n) (\j. d j * abs (G i j))` by
         (rewrite_tac[GSYM SUM_LMUL] >> irule SUM_EQ' >> rpt strip_tac >> BETA_TAC >>
          qpat_x_assum `!j. j < n ==> _` irule >> pop_assum mp_tac >> rewrite_tac[IN_COUNT]) >>
      pop_assum SUBST1_TAC >>
      `0 < d i` by (qpat_x_assum `!i. i < n ==> 0 < d i` irule >> asm_rewrite_tac[]) >>
      `sum (count n) (\j. d j * abs (G i j)) <= 2 * d i * G i i` by
         (qpat_x_assum `!i. i < n ==> sum _ _ <= _` irule >> asm_rewrite_tac[]) >>
      `d i * sum (count n) (\j. d j * abs (G i j)) <= d i * (2 * d i * G i i)` by
         (irule REAL_LE_LMUL_IMP >> asm_rewrite_tac[] >> irule REAL_LT_IMP_LE >> asm_rewrite_tac[]) >>
      pop_assum mp_tac >> SUM_ARITH_TAC)
  >> `dsum n (\i j. x i / d i * (d i * G i j * d j) * (x j / d j)) = dsum n (\i j. x i * G i j * x j)` by
       (irule dsum_eq >> rpt strip_tac >> BETA_TAC >> irule div_cancel >>
        conj_tac >> irule REAL_POS_NZ >> qpat_x_assum `!i. i < n ==> 0 < d i` irule >> asm_rewrite_tac[]) >>
  pop_assum SUBST1_TAC >> disch_then ACCEPT_TAC
QED

(* ================= 4. the Gram part ================= *)

Theorem gram_nonneg[local]:
  !n nk (x:num -> real) (p:num -> num -> real).
    0 <= dsum n (\i j. x i * x j * sum (count nk) (\k. p i k * p j k))
Proof
  rpt gen_tac >>
  `dsum n (\i j. x i * x j * sum (count nk) (\k. p i k * p j k)) =
   dsum n (\i j. sum (count nk) (\k. x i * p i k * (x j * p j k)))` by
     (irule dsum_eq >> rpt strip_tac >> BETA_TAC >> rewrite_tac[GSYM SUM_LMUL] >>
      irule SUM_EQ' >> rpt strip_tac >> BETA_TAC >> SUM_ARITH_TAC) >>
  pop_assum SUBST1_TAC >> rewrite_tac[dsum_def] >> BETA_TAC >>
  `!i. sum (count n) (\j. sum (count nk) (\k. x i * p i k * (x j * p j k))) =
       sum (count nk) (\k. sum (count n) (\j. x i * p i k * (x j * p j k)))` by
     (gen_tac >> qspecl_then [`\j k. x i * p i k * (x j * p j k)`, `n`, `nk`] (ACCEPT_TAC o BETA_RULE) SUM_SWAP_COUNT) >>
  pop_assum (fn th => rewrite_tac[th]) >>
  qspecl_then [`\i k. sum (count n) (\j. x i * p i k * (x j * p j k))`, `n`, `nk`] (SUBST1_TAC o BETA_RULE) SUM_SWAP_COUNT >>
  irule SUM_POS_LE >> rewrite_tac[FINITE_COUNT] >> rpt strip_tac >> BETA_TAC >>
  `sum (count n) (\i. sum (count n) (\j. x i * p i x' * (x j * p j x'))) =
   sum (count n) (\i. x i * p i x') * sum (count n) (\j. x j * p j x')` by
     simp_tac (srw_ss()) [SUM_LMUL, SUM_RMUL] >>
  pop_assum SUBST1_TAC >> rewrite_tac[REAL_LE_SQUARE]
QED

(* ================= 5. from the lists ================= *)

Theorem roi_le[local]:
  !m n. real_of_int m <= real_of_int n <=> m <= n
Proof
  rpt gen_tac >> rewrite_tac[real_of_int_le]
QED

Theorem roi_lt[local]:
  !m n. real_of_int m < real_of_int n <=> m < n
Proof
  rpt gen_tac >> rewrite_tac[real_of_int_lt]
QED

Theorem roi_abs[local]:
  !g:int. real_of_int (if g < 0 then -g else g) = abs (real_of_int g)
Proof
  gen_tac >> Cases_on `g < 0`
  >- (`real_of_int g < 0` by
         (qspecl_then [`g`, `0`] mp_tac roi_lt >> rewrite_tac[real_of_int_num] >>
          disch_then (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
      asm_rewrite_tac[real_of_int_neg] >> pop_assum mp_tac >> REAL_ARITH_TAC)
  >> `~(real_of_int g < 0)` by
        (qspecl_then [`g`, `0`] mp_tac roi_lt >> rewrite_tac[real_of_int_num] >>
         disch_then (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[] >> pop_assum mp_tac >> REAL_ARITH_TAC
QED

Theorem ldot_csum[local]:
  !r (y:real list). LENGTH r = LENGTH y ==>
    ldot r y = sum (count (LENGTH r)) (\j. real_of_int (EL j r) * EL j y)
Proof
  Induct
  >- rewrite_tac[ldot_def, LENGTH, COUNT_ZERO, CONJUNCT1 SUM_CLAUSES]
  >> gen_tac >> Cases
  >- rewrite_tac[LENGTH, SUC_NOT_ZERO]
  >> rewrite_tac[LENGTH, prim_recTheory.INV_SUC_EQ, csum_head] >> strip_tac >>
  rewrite_tac[ldot_def, list_case_def] >> BETA_TAC >> rewrite_tac[EL, HD, TL] >> AP_TERM_TAC >>
  first_x_assum irule >> first_assum ACCEPT_TAC
QED

Theorem qform_csum[local]:
  !Rs (u:real list) (y:real list). LENGTH u = LENGTH Rs ==>
    qform Rs u y = sum (count (LENGTH Rs)) (\i. EL i u * ldot (EL i Rs) y)
Proof
  Induct
  >- rewrite_tac[qform_def, LENGTH, COUNT_ZERO, CONJUNCT1 SUM_CLAUSES]
  >> gen_tac >> Cases
  >- rewrite_tac[LENGTH, SUC_NOT]
  >> rewrite_tac[LENGTH, prim_recTheory.INV_SUC_EQ, csum_head] >> rpt strip_tac >>
  rewrite_tac[qform_def, list_case_def] >> BETA_TAC >> rewrite_tac[EL, HD, TL] >> AP_TERM_TAC >>
  first_x_assum irule >> first_assum ACCEPT_TAC
QED

Theorem dot_acc[local]:
  !xs acc ys. dot acc xs ys = acc + dot 0 xs ys
Proof
  Induct
  >- rewrite_tac[dot_def, INT_ADD_RID]
  >> rpt gen_tac >> Cases_on `ys`
  >- rewrite_tac[dot_def, list_case_def, INT_ADD_RID]
  >> simp_tac bool_ss [dot_def, list_case_def, INT_ADD_LID] >>
  first_assum (qspecl_then [`acc + h * h'`, `t`] SUBST1_TAC) >>
  first_assum (qspecl_then [`h * h'`, `t`] SUBST1_TAC) >>
  rewrite_tac[INT_ADD_ASSOC]
QED

Theorem dot_sym[local]:
  !xs ys. dot 0 xs ys = dot 0 ys xs
Proof
  Induct
  >- (Cases >> rewrite_tac[dot_def, list_case_def])
  >> gen_tac >> Cases
  >- rewrite_tac[dot_def, list_case_def]
  >> simp_tac bool_ss [dot_def, list_case_def, INT_ADD_LID] >>
  once_rewrite_tac[dot_acc] >>
  first_x_assum (qspec_then `t` SUBST1_TAC) >> AP_THM_TAC >> AP_TERM_TAC >> MATCH_ACCEPT_TAC INT_MUL_COMM
QED

Definition pad_def:
  pad (l:int list) (k:num) = if k < LENGTH l then real_of_int (EL k l) else 0
End

Theorem pad_nil[local]:
  !k. pad [] k = 0
Proof
  rewrite_tac[pad_def, LENGTH, prim_recTheory.NOT_LESS_0]
QED

Theorem pad_cons[local]:
  !h t k. pad (h::t) 0 = real_of_int h /\ pad (h::t) (SUC k) = pad t k
Proof
  rewrite_tac[pad_def, LENGTH, LESS_MONO_EQ, EL, HD, TL, prim_recTheory.LESS_0]
QED

Theorem dot_pad[local]:
  !a b K. LENGTH a <= K /\ LENGTH b <= K ==>
    real_of_int (dot 0 a b) = sum (count K) (\k. pad a k * pad b k)
Proof
  Induct
  >- rewrite_tac[dot_def, pad_nil, REAL_MUL_LZERO, SUM_0', real_of_int_num]
  >> gen_tac >> Cases
  >- rewrite_tac[dot_def, list_case_def, pad_nil, REAL_MUL_RZERO, SUM_0', real_of_int_num]
  >> Cases
  >- rewrite_tac[LENGTH, NOT_SUC_LESS_EQ_0]
  >> rewrite_tac[LENGTH, LESS_EQ_MONO] >> strip_tac >>
  rewrite_tac[csum_head] >> simp_tac bool_ss [dot_def, list_case_def, INT_ADD_LID, pad_cons] >>
  once_rewrite_tac[dot_acc] >> rewrite_tac[real_of_int_add, real_of_int_mul] >>
  AP_TERM_TAC >> first_x_assum irule >> asm_rewrite_tac[]
QED

Theorem len_le_sum[local]:
  !(Ls:int list list) i. i < LENGTH Ls ==> LENGTH (EL i Ls) <= SUM (MAP LENGTH Ls)
Proof
  Induct >- rewrite_tac[LENGTH, prim_recTheory.NOT_LESS_0] >>
  gen_tac >> Cases >> rewrite_tac[LENGTH, EL, HD, TL, MAP, SUM, LESS_MONO_EQ] >> strip_tac
  >- (simp_tac arith_ss [])
  >> first_x_assum (qspec_then `n` mp_tac) >> asm_rewrite_tac[] >> simp_tac arith_ss []
QED

Theorem roi_cond[local]:
  !b (x:int). real_of_int (if b then x else 0) = if b then real_of_int x else 0
Proof
  Cases >> rewrite_tac[real_of_int_num]
QED

Theorem rowsum_csum[local]:
  !mrow c1 c2 i j li Ls (ds:num list) acc.
    LENGTH Ls = LENGTH mrow /\ LENGTH ds = LENGTH mrow ==>
    real_of_int (rowsum c1 c2 i j li mrow Ls ds acc) =
    real_of_int acc +
    sum (count (LENGTH mrow)) (\t.
      &(EL t ds) * abs (real_of_int (c1 * EL t mrow - c2 * dot 0 li (EL t Ls))) -
      (if i = j + t then 2 * &(EL t ds) * real_of_int (c1 * EL t mrow - c2 * dot 0 li (EL t Ls)) else 0))
Proof
  Induct
  >- (rpt strip_tac >> once_rewrite_tac[rowsum_def] >>
      rewrite_tac[list_case_def, LENGTH, COUNT_ZERO, CONJUNCT1 SUM_CLAUSES, REAL_ADD_RID])
  >> rpt gen_tac >> Cases_on `Ls`
  >- rewrite_tac[LENGTH, SUC_NOT]
  >> Cases_on `ds`
  >- rewrite_tac[LENGTH, SUC_NOT]
  >> rewrite_tac[LENGTH, prim_recTheory.INV_SUC_EQ] >> strip_tac >>
  once_rewrite_tac[rowsum_def] >> simp_tac bool_ss [list_case_def, LET_THM] >>
  first_x_assum (qspecl_then [`c1`, `c2`, `i`, `j + 1`, `li`, `t`, `t'`,
      `acc + &h'' * (if c1 * h - c2 * dot 0 li h' < 0 then -(c1 * h - c2 * dot 0 li h') else c1 * h - c2 * dot 0 li h') -
       (if i = j then 2 * &h'' * (c1 * h - c2 * dot 0 li h') else 0)`] mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then SUBST1_TAC >>
  rewrite_tac[csum_head] >> BETA_TAC >> rewrite_tac[EL, HD, TL, ADD_CLAUSES] >>
  `!t. (i = j + 1 + t) <=> (i = SUC (j + t))` by (gen_tac >> rewrite_tac[ADD1] >> simp_tac arith_ss []) >>
  pop_assum (fn th => rewrite_tac[th]) >>
  rewrite_tac[real_of_int_add, real_of_int_sub, real_of_int_mul, roi_abs] >>
  rewrite_tac[roi_cond, real_of_int_add, real_of_int_sub, real_of_int_mul, real_of_int_num] >>
  SUM_ARITH_TAC
QED

Theorem dd_rows_el[local]:
  !M c1 c2 i Lrows Lall (ds:num list) dall.
    dd_rows c1 c2 i M Lrows Lall ds dall /\ LENGTH Lrows = LENGTH M /\ LENGTH ds = LENGTH M ==>
    !k. k < LENGTH M ==> 0 < EL k ds /\ rowsum c1 c2 (i + k) 0 (EL k Lrows) (EL k M) Lall dall 0 <= 0
Proof
  Induct
  >- rewrite_tac[LENGTH, prim_recTheory.NOT_LESS_0]
  >> rpt gen_tac >> Cases_on `Lrows`
  >- rewrite_tac[LENGTH, SUC_NOT]
  >> Cases_on `ds`
  >- rewrite_tac[LENGTH, SUC_NOT]
  >> once_rewrite_tac[dd_rows_def] >> simp_tac bool_ss [list_case_def, LENGTH, prim_recTheory.INV_SUC_EQ] >> strip_tac >>
  Cases
  >- (rewrite_tac[EL, HD, ADD_CLAUSES] >> asm_rewrite_tac[])
  >> rewrite_tac[EL, TL, LESS_MONO_EQ] >> strip_tac >>
  first_x_assum (qspecl_then [`c1`, `c2`, `i + 1`, `t`, `Lall`, `t'`, `dall`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspec_then `n` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  `i + 1 + n = i + SUC n` by DECIDE_TAC >>
  pop_assum SUBST1_TAC >> rewrite_tac[]
QED

Theorem sum_delta_f[local]:
  !s a (f:num -> real). sum s (\t. if a = t then f t else 0) = if a IN s then f a else 0
Proof
  rpt gen_tac >>
  `sum s (\t. if a = t then f t else 0) = sum s (\t. if t = a then f a else 0)` by
     (irule SUM_EQ' >> rpt strip_tac >> BETA_TAC >> Cases_on `a = x`
      >- (pop_assum SUBST_ALL_TAC >> rewrite_tac[])
      >> `~(x = a)` by (strip_tac >> qpat_x_assum `~(a = x)` mp_tac >> asm_rewrite_tac[]) >> asm_rewrite_tac[]) >>
  pop_assum SUBST1_TAC >> rewrite_tac[SUM_DELTA]
QED

Theorem final_arith[local]:
  !P c1 Q c2 R:real. P = c1 * Q - c2 * R ==> 0 < c1 ==> 0 <= c2 ==> 0 <= R ==> 0 <= P ==> 0 <= Q
Proof
  rpt strip_tac >>
  `0 <= c2 * R` by (irule REAL_LE_MUL >> conj_tac >> first_assum ACCEPT_TAC) >>
  `0 <= c1 * Q` by (qpat_x_assum `P = _` SUBST_ALL_TAC >> rpt (pop_assum mp_tac) >> SUM_ARITH_TAC) >>
  qspecl_then [`c1`, `0`, `Q`] mp_tac REAL_LE_LMUL >> asm_rewrite_tac[REAL_MUL_RZERO]
QED

(* ================= 6. S040 ================= *)

Theorem S040_as_constants[local]:
  S040
Proof
  rewrite_tac[S040_def] >> rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  `!i. i < LENGTH M ==> LENGTH (EL i M) = LENGTH M` by
     (qpat_x_assum `EVERY _ M` mp_tac >> rewrite_tac[EVERY_EL] >> BETA_TAC >> disch_then ACCEPT_TAC) >>
  (* the rows *)
  `!k. k < LENGTH M ==> 0 < EL k ds /\ rowsum c1 c2 k 0 (EL k Lw) (EL k M) Lw ds 0 <= 0` by
     (qspecl_then [`M`, `c1`, `c2`, `0`, `Lw`, `Lw`, `ds`, `ds`] mp_tac dd_rows_el >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      rewrite_tac[ADD_CLAUSES]) >>
  `!i. i < LENGTH M ==>
     sum (count (LENGTH M)) (\j. &EL j ds * abs (real_of_int (c1 * EL j (EL i M) - c2 * dot 0 (EL i Lw) (EL j Lw))))
     <= 2 * &EL i ds * real_of_int (c1 * EL i (EL i M) - c2 * dot 0 (EL i Lw) (EL i Lw))` by
     (rpt strip_tac >>
      `LENGTH (EL i M) = LENGTH M` by (qpat_x_assum `!i. i < LENGTH M ==> LENGTH (EL i M) = _` irule >> first_assum ACCEPT_TAC) >>
      `rowsum c1 c2 i 0 (EL i Lw) (EL i M) Lw ds 0 <= 0` by
         (qpat_assum `!k. k < LENGTH M ==> 0 < EL k ds /\ _` (qspec_then `i` mp_tac) >>
          impl_tac >- first_assum ACCEPT_TAC >> disch_then (ACCEPT_TAC o CONJUNCT2)) >>
      `real_of_int (rowsum c1 c2 i 0 (EL i Lw) (EL i M) Lw ds 0) <= 0` by
         (qspecl_then [`rowsum c1 c2 i 0 (EL i Lw) (EL i M) Lw ds 0`, `0`] mp_tac roi_le >>
          rewrite_tac[real_of_int_num] >> disch_then (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
      qspecl_then [`EL i M`, `c1`, `c2`, `i`, `0`, `EL i Lw`, `Lw`, `ds`, `0`] mp_tac rowsum_csum >>
      impl_tac >- (qpat_x_assum `LENGTH (EL i M) = _` SUBST1_TAC >> conj_tac >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `LENGTH (EL i M) = _` (fn th => rewrite_tac[th, ADD_CLAUSES, real_of_int_num, REAL_ADD_LID]) >>
      qspecl_then [`count (LENGTH M)`, `i`,
         `\t. 2 * &EL t ds * real_of_int (c1 * EL t (EL i M) - c2 * dot 0 (EL i Lw) (EL t Lw))`]
         (fn th0 => qpat_assum `i < LENGTH M` (fn th => mp_tac (REWRITE_RULE [IN_COUNT, th] (BETA_RULE th0)))) sum_delta_f >>
      qspecl_then [`\t. &EL t ds * abs (real_of_int (c1 * EL t (EL i M) - c2 * dot 0 (EL i Lw) (EL t Lw)))`,
         `\t. if i = t then 2 * &EL t ds * real_of_int (c1 * EL t (EL i M) - c2 * dot 0 (EL i Lw) (EL t Lw)) else 0`,
         `count (LENGTH M)`] (mp_tac o BETA_RULE o REWRITE_RULE [FINITE_COUNT]) SUM_SUB' >>
      qpat_x_assum `real_of_int _ <= 0` mp_tac >> SUM_ARITH_TAC) >>
  `!i j. i < LENGTH M /\ j < LENGTH M ==>
     real_of_int (c1 * EL j (EL i M) - c2 * dot 0 (EL i Lw) (EL j Lw)) =
     real_of_int (c1 * EL i (EL j M) - c2 * dot 0 (EL j Lw) (EL i Lw))` by
     (rpt strip_tac >>
      `EL j (EL i M) = EL i (EL j M)` by
         (qpat_x_assum `!i j. i < LENGTH M /\ j < LENGTH M ==> EL j (EL i M) = _` irule >> conj_tac >> first_assum ACCEPT_TAC) >>
      pop_assum SUBST1_TAC >> qspecl_then [`EL i Lw`, `EL j Lw`] SUBST1_TAC dot_sym >> REFL_TAC) >>
  `0 <= dsum (LENGTH M) (\i j. EL i v * real_of_int (c1 * EL j (EL i M) - c2 * dot 0 (EL i Lw) (EL j Lw)) * EL j v)` by
     (qspecl_then [`LENGTH M`, `\i j. real_of_int (c1 * EL j (EL i M) - c2 * dot 0 (EL i Lw) (EL j Lw))`,
                   `\i. (&EL i ds):real`, `\i. EL i v`] mp_tac wdd_psd >> BETA_TAC >>
      impl_tac >- (rpt conj_tac
          >- first_assum ACCEPT_TAC
          >- (rpt strip_tac >> rewrite_tac[REAL_LT] >>
              qpat_assum `!k. k < LENGTH M ==> 0 < EL k ds /\ _` (qspec_then `i` mp_tac) >>
              impl_tac >- first_assum ACCEPT_TAC >> disch_then (ACCEPT_TAC o CONJUNCT1))
          >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  (* split G into c1 M and c2 Lw Lw^T *)
  `dsum (LENGTH M) (\i j. EL i v * real_of_int (c1 * EL j (EL i M) - c2 * dot 0 (EL i Lw) (EL j Lw)) * EL j v) =
   real_of_int c1 * dsum (LENGTH M) (\i j. EL i v * real_of_int (EL j (EL i M)) * EL j v) -
   real_of_int c2 * dsum (LENGTH M) (\i j. EL i v * EL j v * sum (count (SUM (MAP LENGTH Lw))) (\k. pad (EL i Lw) k * pad (EL j Lw) k))` by
     (qspecl_then [`LENGTH M`, `real_of_int c1`, `\i j. EL i v * real_of_int (EL j (EL i M)) * EL j v`]
         (SUBST1_TAC o SYM o BETA_RULE) dsum_cmul >>
      qspecl_then [`LENGTH M`, `real_of_int c2`,
         `\i j. EL i v * EL j v * sum (count (SUM (MAP LENGTH Lw))) (\k. pad (EL i Lw) k * pad (EL j Lw) k)`]
         (SUBST1_TAC o SYM o BETA_RULE) dsum_cmul >>
      qspecl_then [`LENGTH M`, `\i j. real_of_int c1 * (EL i v * real_of_int (EL j (EL i M)) * EL j v)`,
         `\i j. real_of_int c2 * (EL i v * EL j v * sum (count (SUM (MAP LENGTH Lw))) (\k. pad (EL i Lw) k * pad (EL j Lw) k))`]
         (SUBST1_TAC o SYM o BETA_RULE) dsum_sub >>
      irule dsum_eq >> rpt strip_tac >> BETA_TAC >>
      `real_of_int (dot 0 (EL i Lw) (EL j Lw)) = sum (count (SUM (MAP LENGTH Lw))) (\k. pad (EL i Lw) k * pad (EL j Lw) k)` by
         (irule dot_pad >> conj_tac >> irule len_le_sum >> asm_rewrite_tac[]) >>
      pop_assum (SUBST1_TAC o SYM) >>
      rewrite_tac[real_of_int_sub, real_of_int_mul] >> SUM_ARITH_TAC) >>
  qspecl_then [`LENGTH M`, `SUM (MAP LENGTH Lw)`, `\i. EL i v`, `\i k. pad (EL i Lw) k`] (assume_tac o BETA_RULE) gram_nonneg >>
  `qform M v v = dsum (LENGTH M) (\i j. EL i v * real_of_int (EL j (EL i M)) * EL j v)` by
     (qspecl_then [`M`, `v`, `v`] mp_tac qform_csum >> impl_tac >- first_assum ACCEPT_TAC >>
      disch_then SUBST1_TAC >> rewrite_tac[dsum_def] >> BETA_TAC >>
      irule SUM_EQ' >> rpt strip_tac >> BETA_TAC >>
      `x < LENGTH M` by (pop_assum mp_tac >> rewrite_tac[IN_COUNT]) >>
      `LENGTH (EL x M) = LENGTH M` by (qpat_x_assum `!i. i < LENGTH M ==> LENGTH (EL i M) = _` irule >> first_assum ACCEPT_TAC) >>
      qspecl_then [`EL x M`, `v`] mp_tac ldot_csum >>
      impl_tac >- asm_rewrite_tac[] >>
      disch_then SUBST1_TAC >> qpat_x_assum `LENGTH (EL x M) = _` SUBST1_TAC >>
      rewrite_tac[GSYM SUM_LMUL] >> irule SUM_EQ' >> rpt strip_tac >> BETA_TAC >> SUM_ARITH_TAC) >>
  pop_assum SUBST1_TAC >>
  `0 < real_of_int c1` by
     (qspecl_then [`0`, `c1`] mp_tac roi_lt >> rewrite_tac[real_of_int_num] >>
      disch_then (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  `0 <= real_of_int c2` by
     (qspecl_then [`0`, `c2`] mp_tac roi_le >> rewrite_tac[real_of_int_num] >>
      disch_then (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `dsum _ _ = real_of_int c1 * _ - real_of_int c2 * _` (fn th => mp_tac (MATCH_MP final_arith th)) >>
  rpt (impl_tac >- first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC
QED

Theorem S040 = EQ_MP S040_def S040_as_constants
