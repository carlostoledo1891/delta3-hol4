Theory attempt
Ancestors
  arithmetic list integer real intreal pred_set iterate real_sigma delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

(* ---------- sums over count ---------- *)

Theorem sum_count_suc[local]:
  !n (f:num->real). sum (count (SUC n)) f = sum (count n) f + f n
Proof
  rpt gen_tac >>
  simp_tac (srw_ss()) [COUNT_SUC, SUM_CLAUSES, FINITE_COUNT] >>
  REAL_ARITH_TAC
QED

Theorem count_suc0[local]:
  !n (f:num->real). sum (count (SUC n)) f = f 0 + sum (count n) (\i. f (SUC i))
Proof
  Induct_on `n`
  >- simp_tac (srw_ss()) [COUNT_SUC, SUM_CLAUSES, FINITE_COUNT]
  >> rpt gen_tac
  >> once_rewrite_tac [sum_count_suc]
  >> first_assum (qspec_then `f` SUBST1_TAC)
  >> simp_tac bool_ss []
  >> REAL_ARITH_TAC
QED

(* ---------- the list functions as sums ---------- *)

Theorem ldot_sum[local]:
  !r y. LENGTH r = LENGTH y ==>
        ldot r y = sum (count (LENGTH r)) (\k. real_of_int (EL k r) * EL k y)
Proof
  Induct
  >- simp [ldot_def, SUM_CLAUSES]
  >> rpt gen_tac >> Cases_on `y` >> simp_tac (srw_ss()) [ldot_def]
  >> strip_tac >> first_x_assum (qspec_then `t` mp_tac)
  >> asm_rewrite_tac [] >> disch_then SUBST1_TAC
  >> simp_tac (srw_ss()) [count_suc0]
QED

Theorem qform_sum[local]:
  !M u y. LENGTH M = LENGTH u ==>
        qform M u y = sum (count (LENGTH M)) (\i. EL i u * ldot (EL i M) y)
Proof
  Induct
  >- simp [qform_def, SUM_CLAUSES]
  >> rpt gen_tac >> Cases_on `u` >> simp_tac (srw_ss()) [qform_def]
  >> strip_tac >> first_x_assum (qspecl_then [`t`, `y`] mp_tac)
  >> asm_rewrite_tac [] >> disch_then SUBST1_TAC
  >> simp_tac (srw_ss()) [count_suc0]
QED

Theorem dot_acc[local]:
  !a acc b. dot acc a b = acc + dot 0 a b
Proof
  Induct
  >- simp [dot_def]
  >> rpt gen_tac >> Cases_on `b` >> simp_tac (srw_ss()) [dot_def]
  >> first_assum (qspecl_then [`acc + h * h'`, `t`] SUBST1_TAC)
  >> first_assum (qspecl_then [`h * h'`, `t`] SUBST1_TAC)
  >> simp_tac (srw_ss()) [integerTheory.INT_ADD_ASSOC]
QED

Theorem dot_comm[local]:
  !a acc b. dot acc a b = dot acc b a
Proof
  Induct
  >- (rpt gen_tac >> Cases_on `b` >> simp [dot_def])
  >> rpt gen_tac >> Cases_on `b` >> simp_tac (srw_ss()) [dot_def]
  >> first_assum (qspecl_then [`acc + h * h'`, `t`] SUBST1_TAC)
  >> simp_tac (srw_ss()) [integerTheory.INT_MUL_COMM]
QED

Theorem real_of_int_ABS[local]:
  !g:int. real_of_int (ABS g) = abs (real_of_int g)
Proof
  gen_tac >> rewrite_tac [integerTheory.INT_ABS, realTheory.abs] >>
  Cases_on `g < 0` >> asm_rewrite_tac []
  >- (`real_of_int g < real_of_int 0` by asm_rewrite_tac [real_of_int_lt] >>
      pop_assum mp_tac >> rewrite_tac [real_of_int_num, real_of_int_neg] >> strip_tac >>
      `~(0 <= real_of_int g)` by (pop_assum mp_tac >> REAL_ARITH_TAC) >>
      asm_rewrite_tac [])
  >> `real_of_int 0 <= real_of_int g` by (rewrite_tac [real_of_int_le] >> pop_assum mp_tac >> intLib.ARITH_TAC)
  >> pop_assum mp_tac >> rewrite_tac [real_of_int_num] >> strip_tac >> asm_rewrite_tac []
QED

Theorem real_of_int_cond[local]:
  !b x y. real_of_int (if b then x else y) = if b then real_of_int x else real_of_int y
Proof
  rw []
QED

Theorem add_suc[local]:
  !j k. j + SUC k = j + 1 + k
Proof
  rpt gen_tac >> decide_tac
QED

Theorem rowsum_real[local]:
  !mrow (c1:int) c2 i j li Ls ds acc.
    LENGTH Ls = LENGTH mrow /\ LENGTH ds = LENGTH mrow ==>
    real_of_int (rowsum c1 c2 i j li mrow Ls ds acc) =
    real_of_int acc +
    sum (count (LENGTH mrow))
      (\k. &(EL k ds) * abs (real_of_int c1 * real_of_int (EL k mrow) - real_of_int c2 * real_of_int (dot 0 li (EL k Ls))) -
           (if i = j + k then 2 * &(EL k ds) * (real_of_int c1 * real_of_int (EL k mrow) - real_of_int c2 * real_of_int (dot 0 li (EL k Ls))) else 0))
Proof
  Induct
  >- (rpt gen_tac >> once_rewrite_tac [rowsum_def] >> simp_tac bool_ss [list_case_def] >>
      simp_tac (srw_ss()) [SUM_CLAUSES])
  >> rpt gen_tac >> Cases_on `Ls` >> Cases_on `ds`
  >> rewrite_tac [LENGTH, numTheory.NOT_SUC, SUC_NOT, prim_recTheory.INV_SUC_EQ] >> strip_tac
  >> once_rewrite_tac [rowsum_def] >> simp_tac bool_ss [list_case_def, LET_THM]
  >> rewrite_tac [GSYM integerTheory.INT_ABS]
  >> qmatch_goalsub_abbrev_tac `rowsum _ _ _ _ _ _ _ _ acc1`
  >> first_x_assum (qspecl_then [`c1`, `c2`, `i`, `j + 1`, `li`, `t`, `t'`, `acc1`] mp_tac)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then SUBST1_TAC
  >> qunabbrev_tac `acc1`
  >> rewrite_tac [count_suc0] >> BETA_TAC
  >> rewrite_tac [real_of_int_add, real_of_int_sub, real_of_int_mul, real_of_int_num, real_of_int_ABS,
                  real_of_int_cond, EL, HD, TL, ADD_0, add_suc]
  >> rewrite_tac [real_sub, REAL_ADD_ASSOC]
QED

Theorem dd_rows_el[local]:
  !M (c1:int) c2 i Lrows Lall ds dall.
    dd_rows c1 c2 i M Lrows Lall ds dall ==>
    !k. k < LENGTH M ==> 0 < EL k ds /\ rowsum c1 c2 (i + k) 0 (EL k Lrows) (EL k M) Lall dall 0 <= 0
Proof
  Induct
  >- simp []
  >> rpt gen_tac >> Cases_on `Lrows` >> Cases_on `ds`
  >> once_rewrite_tac [dd_rows_def] >> simp_tac bool_ss [list_case_def]
  >> strip_tac >> Cases >> rewrite_tac [EL, HD, TL, LENGTH, LESS_MONO_EQ, ADD_0]
  >- asm_rewrite_tac []
  >> strip_tac >> first_x_assum drule >> disch_then (qspec_then `n` mp_tac)
  >> asm_rewrite_tac [] >> `i + 1 + n = i + SUC n` by decide_tac >> asm_rewrite_tac []
QED

Theorem sdd_rows_el[local]:
  !M (c1:int) c2 i Lrows Lall ds dall.
    sdd_rows c1 c2 i M Lrows Lall ds dall ==>
    !k. k < LENGTH M ==> 0 < EL k ds /\ rowsum c1 c2 (i + k) 0 (EL k Lrows) (EL k M) Lall dall 0 < 0
Proof
  Induct
  >- simp []
  >> rpt gen_tac >> Cases_on `Lrows` >> Cases_on `ds`
  >> once_rewrite_tac [sdd_rows_def] >> simp_tac bool_ss [list_case_def]
  >> strip_tac >> Cases >> rewrite_tac [EL, HD, TL, LENGTH, LESS_MONO_EQ, ADD_0]
  >- asm_rewrite_tac []
  >> strip_tac >> first_x_assum drule >> disch_then (qspec_then `n` mp_tac)
  >> asm_rewrite_tac [] >> `i + 1 + n = i + SUC n` by decide_tac >> asm_rewrite_tac []
QED

(* ---------- the Gram part: c2 * Lw Lw^T is positive semidefinite ---------- *)

Definition padv_def:
  padv (r:int list) (k:num) = if k < LENGTH r then real_of_int (EL k r) else (0:real)
End

Theorem dot_real[local]:
  !a b kk. LENGTH a <= kk /\ LENGTH b <= kk ==>
    real_of_int (dot 0 a b) = sum (count kk) (\k. padv a k * padv b k)
Proof
  Induct
  >- simp [dot_def, padv_def, SUM_0']
  >> rpt gen_tac >> Cases_on `b`
  >- simp [dot_def, padv_def, SUM_0']
  >> Cases_on `kk` >- simp []
  >> simp_tac (srw_ss()) [dot_def] >> strip_tac
  >> once_rewrite_tac [dot_acc]
  >> simp_tac (srw_ss()) [count_suc0, padv_def]
  >> first_x_assum (qspecl_then [`t`, `n`] mp_tac) >> asm_simp_tac (srw_ss()) [padv_def]
QED

Theorem sum_mul_sum[local]:
  !n m (f:num->real) g. sum (count n) f * sum (count m) g = sum (count n) (\i. sum (count m) (\j. f i * g j))
Proof
  simp [SUM_LMUL, SUM_RMUL]
QED

Theorem gram_eq[local]:
  !n kk (a:num->num->real) (w:num->real).
    sum (count n) (\i. sum (count n) (\j. w i * w j * sum (count kk) (\k. a i k * a j k))) =
    sum (count kk) (\k. sum (count n) (\i. w i * a i k) * sum (count n) (\j. w j * a j k))
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [sum_mul_sum] >>
  CONV_TAC (RAND_CONV (HO_REWR_CONV SUM_SWAP_COUNT)) >> simp_tac bool_ss [] >>
  irule SUM_EQ_COUNT >> rpt strip_tac >> simp_tac bool_ss [] >>
  CONV_TAC (RAND_CONV (HO_REWR_CONV SUM_SWAP_COUNT)) >> simp_tac bool_ss [] >>
  irule SUM_EQ_COUNT >> rpt strip_tac >> simp_tac bool_ss [] >>
  simp_tac (srw_ss()) [GSYM SUM_LMUL] >>
  irule SUM_EQ_COUNT >> rpt strip_tac >> simp_tac bool_ss [] >> REAL_ARITH_TAC
QED

Theorem gram_psd[local]:
  !n kk (L:int list list) (v:real list). (!i. i < n ==> LENGTH (EL i L) <= kk) ==>
    0 <= sum (count n) (\i. sum (count n) (\j. EL i v * EL j v * real_of_int (dot 0 (EL i L) (EL j L))))
Proof
  rpt strip_tac >>
  `sum (count n) (\i. sum (count n) (\j. EL i v * EL j v * real_of_int (dot 0 (EL i L) (EL j L)))) =
   sum (count n) (\i. sum (count n) (\j. EL i v * EL j v * sum (count kk) (\k. padv (EL i L) k * padv (EL j L) k)))`
    by (irule SUM_EQ_COUNT >> rpt strip_tac >> simp_tac bool_ss [] >>
        irule SUM_EQ_COUNT >> rpt strip_tac >> simp_tac bool_ss [] >>
        AP_TERM_TAC >> irule dot_real >> conj_tac >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  pop_assum SUBST1_TAC >>
  qspecl_then [`n`, `kk`, `\i k. padv (EL i L) k`, `\i. EL i v`] mp_tac gram_eq >>
  simp_tac bool_ss [] >> disch_then SUBST1_TAC >>
  irule SUM_POS_LE >> simp_tac bool_ss [REAL_LE_SQUARE]
QED

Theorem rows_bound[local]:
  !L:int list list. ?bk. !i. i < LENGTH L ==> LENGTH (EL i L) <= bk
Proof
  Induct >- simp [] >>
  gen_tac >> pop_assum strip_assume_tac >> qexists_tac `MAX (LENGTH h) bk` >>
  Cases >> simp_tac (srw_ss()) [] >> rw [arithmeticTheory.MAX_DEF] >> res_tac >> decide_tac
QED

(* ---------- the weighted-dominance inequality, for real matrices ---------- *)

Theorem pw_aux[local]:
  !g p q:real. 0 <= 2 * g * p * q + abs g * (p * p + q * q)
Proof
  rpt gen_tac >> Cases_on `0 <= g`
  >- (`abs g = g` by asm_simp_tac (srw_ss()) [realTheory.abs] >> pop_assum SUBST1_TAC >>
      `2 * g * p * q + g * (p * p + q * q) = g * ((p + q) * (p + q))` by REAL_ARITH_TAC >>
      pop_assum SUBST1_TAC >> match_mp_tac REAL_LE_MUL >> asm_rewrite_tac [REAL_LE_SQUARE])
  >> `abs g = -g` by asm_simp_tac (srw_ss()) [realTheory.abs] >> pop_assum SUBST1_TAC
  >> `2 * g * p * q + -g * (p * p + q * q) = -g * ((p - q) * (p - q))` by REAL_ARITH_TAC
  >> pop_assum SUBST1_TAC >> match_mp_tac REAL_LE_MUL
  >> `0 <= -g` by REAL_ASM_ARITH_TAC
  >> asm_rewrite_tac [REAL_LE_SQUARE]
QED

Theorem pw_off_eq[local]:
  !g ag p q a b:real.
    g * (a * p) * (b * q) + a * (p * p) * (b * ag) + (g * (b * q) * (a * p) + b * (q * q) * (a * ag)) =
    (a * b) * (2 * g * p * q + ag * (p * p + q * q))
Proof
  REAL_ARITH_TAC
QED

Theorem pw_off[local]:
  !g p q a b:real. 0 < a /\ 0 < b ==>
    0 <= g * (a * p) * (b * q) + a * (p * p) * (b * abs g) +
         (g * (b * q) * (a * p) + b * (q * q) * (a * abs g))
Proof
  rpt strip_tac >> rewrite_tac [pw_off_eq] >> match_mp_tac REAL_LE_MUL >> conj_tac
  >- (match_mp_tac REAL_LE_MUL >> conj_tac >> match_mp_tac REAL_LT_IMP_LE >> first_assum ACCEPT_TAC)
  >> MATCH_ACCEPT_TAC pw_aux
QED

Theorem pw_diag_eq[local]:
  !g ag p a:real.
    g * (a * p) * (a * p) + a * (p * p) * (a * ag - 2 * a * g) +
    (g * (a * p) * (a * p) + a * (p * p) * (a * ag - 2 * a * g)) =
    (2 * ((a * p) * (a * p))) * (ag - g)
Proof
  REAL_ARITH_TAC
QED

Theorem pw_diag[local]:
  !g p a:real.
    0 <= g * (a * p) * (a * p) + a * (p * p) * (a * abs g - 2 * a * g) +
         (g * (a * p) * (a * p) + a * (p * p) * (a * abs g - 2 * a * g))
Proof
  rpt gen_tac >> rewrite_tac [pw_diag_eq] >> match_mp_tac REAL_LE_MUL >> conj_tac
  >- (match_mp_tac REAL_LE_MUL >> simp_tac (srw_ss()) [REAL_LE_SQUARE])
  >> `g <= abs g` by rewrite_tac [ABS_LE]
  >> pop_assum mp_tac >> qspec_tac (`abs g`, `ag`) >> REAL_ARITH_TAC
QED

Theorem sym_pos[local]:
  !n (cc:num->num->real). (!i j. i < n /\ j < n ==> 0 <= cc i j + cc j i) ==>
    0 <= sum (count n) (\i. sum (count n) (\j. cc i j))
Proof
  rpt strip_tac >>
  `sum (count n) (\i. sum (count n) (\j. cc j i)) = sum (count n) (\i. sum (count n) (\j. cc i j))`
     by (qspecl_then [`\i j. cc i j`, `n`, `n`] mp_tac SUM_SWAP_COUNT >> BETA_TAC >>
         disch_then (ACCEPT_TAC o SYM)) >>
  `sum (count n) (\i. sum (count n) (\j. cc i j + cc j i)) =
   sum (count n) (\i. sum (count n) (\j. cc i j)) + sum (count n) (\i. sum (count n) (\j. cc j i))`
     by simp_tac bool_ss [SUM_ADD_COUNT] >>
  `0 <= sum (count n) (\i. sum (count n) (\j. cc i j + cc j i))`
    by (irule SUM_POS_LE >> simp_tac bool_ss [IN_COUNT] >> rpt strip_tac >>
        irule SUM_POS_LE >> simp_tac bool_ss [IN_COUNT] >> rpt strip_tac >>
        first_x_assum irule >> asm_rewrite_tac []) >>
  pop_assum mp_tac >> pop_assum SUBST1_TAC >> pop_assum SUBST1_TAC >>
  qspec_tac (`sum (count n) (\i. sum (count n) (\j. cc i j))`, `s`) >> REAL_ARITH_TAC
QED

Theorem core[local]:
  !n (G:num->num->real) (d:num->real) (x:num->real).
    (!i j. i < n /\ j < n ==> G i j = G j i) /\ (!i. i < n ==> 0 < d i) ==>
    0 <= sum (count n) (\i. sum (count n) (\j. G i j * (d i * x i) * (d j * x j) +
             d i * (x i * x i) * (d j * abs (G i j) - (if i = j then 2 * d j * G i j else 0))))
Proof
  rpt strip_tac >> ho_match_mp_tac sym_pos >> simp_tac bool_ss [] >> rpt strip_tac >>
  Cases_on `i = j`
  >- (pop_assum SUBST_ALL_TAC >> simp_tac bool_ss [] >> MATCH_ACCEPT_TAC pw_diag)
  >> `~(j = i)` by (strip_tac >> qpat_x_assum `~(i = j)` mp_tac >> asm_rewrite_tac [])
  >> `G j i = G i j` by (first_x_assum irule >> asm_rewrite_tac [])
  >> asm_rewrite_tac [REAL_SUB_RZERO]
  >> irule pw_off >> conj_tac >> first_x_assum irule >> asm_rewrite_tac []
QED

Theorem core2[local]:
  !n (G:num->num->real) (d:num->real) (x:num->real).
    (!i j. i < n /\ j < n ==> G i j = G j i) /\ (!i. i < n ==> 0 < d i) ==>
    0 <= sum (count n) (\i. sum (count n) (\j. G i j * (d i * x i) * (d j * x j))) +
         sum (count n) (\i. d i * (x i * x i) *
                sum (count n) (\j. d j * abs (G i j) - (if i = j then 2 * d j * G i j else 0)))
Proof
  rpt strip_tac >> qspecl_then [`n`, `G`, `d`, `x`] mp_tac core >> asm_rewrite_tac [] >>
  simp_tac (srw_ss()) [SUM_ADD_COUNT, SUM_LMUL]
QED
(* ---------- the matrix of the check ---------- *)

Definition Gm_def:
  Gm (c1:int) (c2:int) (M:int list list) (Lw:int list list) (i:num) (j:num) =
    real_of_int c1 * real_of_int (EL j (EL i M)) -
    real_of_int c2 * real_of_int (dot 0 (EL i Lw) (EL j Lw))
End

Definition dw_def:
  dw (ds:num list) (i:num) = (&(EL i ds)):real
End

Definition xw_def:
  xw (v:real list) (ds:num list) (i:num) = EL i v / &(EL i ds)
End

Theorem qform_split[local]:
  !M Lw (c1:int) (c2:int) (v:real list).
    EVERY (\r. LENGTH r = LENGTH M) M /\ LENGTH v = LENGTH M ==>
    sum (count (LENGTH M)) (\i. sum (count (LENGTH M)) (\j. Gm c1 c2 M Lw i j * EL i v * EL j v)) =
    real_of_int c1 * qform M v v -
    real_of_int c2 * sum (count (LENGTH M)) (\i. sum (count (LENGTH M))
                         (\j. EL i v * EL j v * real_of_int (dot 0 (EL i Lw) (EL j Lw))))
Proof
  rpt strip_tac >>
  `qform M v v = sum (count (LENGTH M)) (\i. sum (count (LENGTH M)) (\j. EL i v * (real_of_int (EL j (EL i M)) * EL j v)))`
     by (asm_simp_tac bool_ss [qform_sum] >> irule SUM_EQ_COUNT >> rpt strip_tac >>
         simp_tac bool_ss [] >>
         `LENGTH (EL i M) = LENGTH v` by fs [EVERY_EL] >>
         drule ldot_sum >> disch_then SUBST1_TAC >> asm_rewrite_tac [] >>
         simp_tac bool_ss [SUM_LMUL]) >>
  pop_assum SUBST1_TAC >>
  `!i. sum (count (LENGTH M)) (\j. Gm c1 c2 M Lw i j * EL i v * EL j v) =
       real_of_int c1 * sum (count (LENGTH M)) (\j. EL i v * (real_of_int (EL j (EL i M)) * EL j v)) -
       real_of_int c2 * sum (count (LENGTH M)) (\j. EL i v * EL j v * real_of_int (dot 0 (EL i Lw) (EL j Lw)))`
     by (gen_tac >>
         `sum (count (LENGTH M)) (\j. Gm c1 c2 M Lw i j * EL i v * EL j v) =
          sum (count (LENGTH M)) (\j. real_of_int c1 * (EL i v * (real_of_int (EL j (EL i M)) * EL j v)) -
                                      real_of_int c2 * (EL i v * EL j v * real_of_int (dot 0 (EL i Lw) (EL j Lw))))`
            by (irule SUM_EQ_COUNT >> rpt strip_tac >> simp_tac bool_ss [Gm_def] >> REAL_ARITH_TAC) >>
         pop_assum SUBST1_TAC >> simp_tac bool_ss [SUM_SUB', FINITE_COUNT, SUM_LMUL]) >>
  asm_simp_tac bool_ss [SUM_SUB', FINITE_COUNT, SUM_LMUL]
QED

Theorem key[local]:
  !M Lw ds (c1:int) (c2:int) (v:real list).
    LENGTH Lw = LENGTH M /\ LENGTH ds = LENGTH M /\ EVERY (\r. LENGTH r = LENGTH M) M /\
    (!i j. i < LENGTH M /\ j < LENGTH M ==> EL j (EL i M) = EL i (EL j M)) /\ 0 <= c2 /\
    (!i. i < LENGTH M ==> 0 < EL i ds) /\ LENGTH v = LENGTH M ==>
    -sum (count (LENGTH M)) (\i. dw ds i * (xw v ds i * xw v ds i) *
          real_of_int (rowsum c1 c2 i 0 (EL i Lw) (EL i M) Lw ds 0))
    <= real_of_int c1 * qform M v v
Proof
  rpt strip_tac >>
  `!i. i < LENGTH M ==>
       real_of_int (rowsum c1 c2 i 0 (EL i Lw) (EL i M) Lw ds 0) =
       sum (count (LENGTH M)) (\j. dw ds j * abs (Gm c1 c2 M Lw i j) -
                                   (if i = j then 2 * dw ds j * Gm c1 c2 M Lw i j else 0))`
    by (rpt strip_tac >>
        `LENGTH (EL i M) = LENGTH M` by fs [EVERY_EL] >>
        qspecl_then [`EL i M`, `c1`, `c2`, `i`, `0`, `EL i Lw`, `Lw`, `ds`, `0`] mp_tac rowsum_real >>
        asm_rewrite_tac [] >> disch_then SUBST1_TAC >>
        rewrite_tac [real_of_int_num, REAL_ADD_LID, ADD_CLAUSES] >>
        irule SUM_EQ_COUNT >> rpt strip_tac >> simp_tac bool_ss [Gm_def, dw_def]) >>
  `!i. i < LENGTH M ==> dw ds i * xw v ds i = EL i v`
    by (rpt strip_tac >> rewrite_tac [dw_def, xw_def] >> irule REAL_DIV_LMUL >>
        `0 < EL i ds` by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
        rewrite_tac [REAL_OF_NUM_EQ] >> strip_tac >> fs []) >>
  qspecl_then [`LENGTH M`, `Gm c1 c2 M Lw`, `dw ds`, `xw v ds`] mp_tac core2 >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> rewrite_tac [Gm_def] >>
          `EL j (EL i M) = EL i (EL j M)` by (first_x_assum irule >> asm_rewrite_tac []) >>
          pop_assum SUBST1_TAC >>
          `dot 0 (EL i Lw) (EL j Lw) = dot 0 (EL j Lw) (EL i Lw)` by MATCH_ACCEPT_TAC dot_comm >>
          pop_assum SUBST1_TAC >> rewrite_tac [])
      >> rpt strip_tac >> rewrite_tac [dw_def] >>
         `0 < EL i ds` by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
         asm_simp_tac (srw_ss()) [REAL_OF_NUM_LT]) >>
  `sum (count (LENGTH M)) (\i. sum (count (LENGTH M)) (\j. Gm c1 c2 M Lw i j * (dw ds i * xw v ds i) * (dw ds j * xw v ds j))) =
   sum (count (LENGTH M)) (\i. sum (count (LENGTH M)) (\j. Gm c1 c2 M Lw i j * EL i v * EL j v))`
    by (irule SUM_EQ_COUNT >> rpt strip_tac >> simp_tac bool_ss [] >>
        irule SUM_EQ_COUNT >> rpt strip_tac >> simp_tac bool_ss [] >> res_tac >> asm_rewrite_tac []) >>
  `sum (count (LENGTH M)) (\i. dw ds i * (xw v ds i * xw v ds i) *
       sum (count (LENGTH M)) (\j. dw ds j * abs (Gm c1 c2 M Lw i j) -
                                   (if i = j then 2 * dw ds j * Gm c1 c2 M Lw i j else 0))) =
   sum (count (LENGTH M)) (\i. dw ds i * (xw v ds i * xw v ds i) *
          real_of_int (rowsum c1 c2 i 0 (EL i Lw) (EL i M) Lw ds 0))`
    by (irule SUM_EQ_COUNT >> rpt strip_tac >> BETA_TAC >> AP_TERM_TAC >>
        CONV_TAC SYM_CONV >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  asm_rewrite_tac [] >> strip_tac >>
  qspecl_then [`M`, `Lw`, `c1`, `c2`, `v`] mp_tac qform_split >> asm_rewrite_tac [] >> strip_tac >>
  qspec_then `Lw` strip_assume_tac rows_bound >>
  qspecl_then [`LENGTH M`, `bk`, `Lw`, `v`] mp_tac gram_psd >>
  impl_tac >- (rpt strip_tac >> first_x_assum irule >> asm_rewrite_tac []) >>
  strip_tac >>
  `0 <= real_of_int c2` by (`real_of_int 0 <= real_of_int c2` by asm_rewrite_tac [real_of_int_le] >>
                            pop_assum mp_tac >> rewrite_tac [real_of_int_num]) >>
  `0 <= real_of_int c2 * sum (count (LENGTH M)) (\i. sum (count (LENGTH M))
                         (\j. EL i v * EL j v * real_of_int (dot 0 (EL i Lw) (EL j Lw))))`
    by (match_mp_tac REAL_LE_MUL >> asm_rewrite_tac []) >>
  rpt (qpat_x_assum `!i. _` kall_tac) >>
  rpt (qpat_x_assum `EVERY _ _` kall_tac) >>
  qpat_x_assum `sum _ _ = _ - _` mp_tac >>
  qpat_x_assum `0 <= _ + _` mp_tac >>
  qpat_x_assum `0 <= _ * _` mp_tac >>
  qspec_tac (`real_of_int c2 * sum (count (LENGTH M)) (\i. sum (count (LENGTH M))
                         (\j. EL i v * EL j v * real_of_int (dot 0 (EL i Lw) (EL j Lw))))`, `P`) >>
  qspec_tac (`real_of_int c1 * qform M v v`, `q`) >>
  qspec_tac (`sum (count (LENGTH M)) (\i. dw ds i * (xw v ds i * xw v ds i) *
          real_of_int (rowsum c1 c2 i 0 (EL i Lw) (EL i M) Lw ds 0))`, `b`) >>
  qspec_tac (`sum (count (LENGTH M)) (\i. sum (count (LENGTH M)) (\j. Gm c1 c2 M Lw i j * EL i v * EL j v))`, `a`) >>
  REAL_ARITH_TAC
QED

(* ---------- small real facts ---------- *)

Theorem rint_le0[local]:
  !r:int. r <= 0 ==> real_of_int r <= 0
Proof
  rpt strip_tac >> `real_of_int r <= real_of_int 0` by asm_rewrite_tac [real_of_int_le] >>
  pop_assum mp_tac >> rewrite_tac [real_of_int_num]
QED

Theorem rint_lt0[local]:
  !r:int. r < 0 ==> real_of_int r < 0
Proof
  rpt strip_tac >> `real_of_int r < real_of_int 0` by asm_rewrite_tac [real_of_int_lt] >>
  pop_assum mp_tac >> rewrite_tac [real_of_int_num]
QED

Theorem term_nn[local]:
  !a x r:real. 0 <= a /\ r <= 0 ==> 0 <= -(a * (x * x) * r)
Proof
  rpt strip_tac >> `-(a * (x * x) * r) = (a * (x * x)) * -r` by REAL_ARITH_TAC >>
  pop_assum SUBST1_TAC >> match_mp_tac REAL_LE_MUL >> conj_tac
  >- (match_mp_tac REAL_LE_MUL >> asm_rewrite_tac [REAL_LE_SQUARE])
  >> pop_assum mp_tac >> REAL_ARITH_TAC
QED

Theorem sq_pos[local]:
  !x:real. ~(x = 0) ==> 0 < x * x
Proof
  rpt strip_tac >> rewrite_tac [REAL_LT_LE, REAL_LE_SQUARE] >> strip_tac >>
  `x * x = 0` by (pop_assum (SUBST1_TAC o SYM) >> rewrite_tac []) >>
  fs [REAL_ENTIRE]
QED

Theorem term_pos[local]:
  !a x r:real. 0 < a /\ ~(x = 0) /\ r < 0 ==> 0 < -(a * (x * x) * r)
Proof
  rpt strip_tac >> `-(a * (x * x) * r) = (a * (x * x)) * -r` by REAL_ARITH_TAC >>
  pop_assum SUBST1_TAC >> match_mp_tac REAL_LT_MUL >> conj_tac
  >- (match_mp_tac REAL_LT_MUL >> asm_rewrite_tac [] >> irule sq_pos >> first_assum ACCEPT_TAC)
  >> pop_assum mp_tac >> REAL_ARITH_TAC
QED

Theorem rint_pos[local]:
  !c:int. 0 < c ==> 0 < real_of_int c
Proof
  rpt strip_tac >> `real_of_int 0 < real_of_int c` by asm_rewrite_tac [real_of_int_lt] >>
  pop_assum mp_tac >> rewrite_tac [real_of_int_num]
QED

Theorem lhs_nn[local]:
  !M Lw ds (c1:int) (c2:int) (v:real list).
    (!i. i < LENGTH M ==> rowsum c1 c2 i 0 (EL i Lw) (EL i M) Lw ds 0 <= 0) ==>
    0 <= -sum (count (LENGTH M)) (\i. dw ds i * (xw v ds i * xw v ds i) *
          real_of_int (rowsum c1 c2 i 0 (EL i Lw) (EL i M) Lw ds 0))
Proof
  rpt strip_tac >> simp_tac bool_ss [GSYM SUM_NEG'] >>
  irule SUM_POS_LE >> simp_tac bool_ss [IN_COUNT] >> rpt strip_tac >>
  match_mp_tac term_nn >> rewrite_tac [dw_def, REAL_POS] >>
  match_mp_tac rint_le0 >> first_x_assum irule >> first_assum ACCEPT_TAC
QED

Theorem lhs_pos[local]:
  !M Lw ds (c1:int) (c2:int) (v:real list) k.
    (!i. i < LENGTH M ==> 0 < EL i ds /\ rowsum c1 c2 i 0 (EL i Lw) (EL i M) Lw ds 0 < 0) /\
    k < LENGTH M /\ ~(EL k v = 0) ==>
    0 < -sum (count (LENGTH M)) (\i. dw ds i * (xw v ds i * xw v ds i) *
          real_of_int (rowsum c1 c2 i 0 (EL i Lw) (EL i M) Lw ds 0))
Proof
  rpt strip_tac >> simp_tac bool_ss [GSYM SUM_NEG'] >>
  match_mp_tac SUM_POS_LT >> conj_tac >- rewrite_tac [FINITE_COUNT] >>
  conj_tac
  >- (simp_tac bool_ss [IN_COUNT] >> rpt strip_tac >>
      match_mp_tac term_nn >> rewrite_tac [dw_def, REAL_POS] >>
      match_mp_tac rint_le0 >> match_mp_tac integerTheory.INT_LT_IMP_LE >>
      first_x_assum (qspec_then `x` mp_tac) >> asm_rewrite_tac [] >> strip_tac >> asm_rewrite_tac [])
  >> qexists_tac `k` >> simp_tac bool_ss [IN_COUNT] >> asm_rewrite_tac [] >>
  first_x_assum (qspec_then `k` mp_tac) >> asm_rewrite_tac [] >> strip_tac >>
  match_mp_tac term_pos >> rewrite_tac [dw_def] >> rpt conj_tac
  >| [asm_rewrite_tac [REAL_OF_NUM_LT],
      rewrite_tac [xw_def] >> strip_tac >>
      `&(EL k ds) * (EL k v / &(EL k ds)) = EL k v`
         by (match_mp_tac REAL_DIV_LMUL >> rewrite_tac [REAL_OF_NUM_EQ] >> strip_tac >> fs []) >>
      metis_tac [REAL_MUL_RZERO],
      match_mp_tac rint_lt0 >> first_assum ACCEPT_TAC]
QED

Theorem S040_as_constants[local]:
  S040
Proof
  rewrite_tac [S040_def] >> rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  drule dd_rows_el >> rewrite_tac [ADD_CLAUSES] >> strip_tac >>
  `!i. i < LENGTH M ==> 0 < EL i ds` by metis_tac [] >>
  `!i. i < LENGTH M ==> rowsum c1 c2 i 0 (EL i Lw) (EL i M) Lw ds 0 <= 0` by metis_tac [] >>
  qspecl_then [`M`, `Lw`, `ds`, `c1`, `c2`, `v`] mp_tac key >> asm_rewrite_tac [] >> strip_tac >>
  qspecl_then [`M`, `Lw`, `ds`, `c1`, `c2`, `v`] mp_tac lhs_nn >> asm_rewrite_tac [] >> strip_tac >>
  `0 <= real_of_int c1 * qform M v v` by metis_tac [REAL_LE_TRANS] >>
  `0 < real_of_int c1` by (irule rint_pos >> first_assum ACCEPT_TAC) >>
  qspecl_then [`real_of_int c1`, `0`, `qform M v v`] mp_tac REAL_LE_LMUL >>
  asm_simp_tac bool_ss [REAL_MUL_RZERO]
QED

Theorem S040 = EQ_MP S040_def S040_as_constants

