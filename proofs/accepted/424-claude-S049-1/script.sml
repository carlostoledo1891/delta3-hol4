Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib

(* S049: the top inner theorem.  With n = LENGTH grid - 1, st = inner_poly ... = (ok,k,g,Cm,mL,mY,mM)
   and ws = widths grid, for y in the box with m = mval grid y <= rin:
     S105: st_val ws st y = D (L0 - M), M = the multiplier terms, and M >= 0 (0 <= m by S115);
     k = 0 and the linear part lin mL ws g is all zero (S058), so st_val ws st y = Q, the quadratic part;
     S109: P = y^T (inner_matrix ws st) y = 2 Q, and the matrix is n x n and symmetric (S078: |ws| = n);
     S046: strict dominance (inner_check's sdd_rows) gives P >= 0, and P > 0 unless y = 0.
   So D (L0 - M) = Q >= 0 gives L0 >= M >= 0, and L0 = 0 forces M = 0, Q = 0, P = 0, y = 0. *)

fun dep_th def = UNDISCH (#1 (EQ_IMP_RULE def));

fun spec_names al th =
  let
    val (vs, _) = strip_forall (concl th)
    fun pick v = case List.find (fn (s, _) => s = fst (dest_var v)) al of
                   SOME (_, t) => t
                 | NONE => v
  in SPECL (map pick vs) th end;

val S078_th = dep_th S078_def;
val S046_th = dep_th S046_def;
val S105_th = dep_th S105_def;
val S109_th = dep_th S109_def;
val S058_th = dep_th S058_def;
val S115_th = dep_th S115_def;

Theorem tuple7[local]:
  !(x:'a # 'b # 'c # 'd # 'e # 'f # 'g). ?ok k g Cm mL mY mM. x = (ok,k,g,Cm,mL,mY,mM)
Proof
  gen_tac >> PairCases_on `x` >> FIRST [metis_tac[] >> NO_TAC, simp[]]
QED

Theorem final_real[local]:
  !dd ll mm qq pp:real.
    0 < dd /\ qq = dd * (ll - mm) /\ 0 <= mm /\ pp = 2 * qq /\ 0 <= pp ==>
    0 <= ll /\ (ll = 0 ==> pp = 0)
Proof
  rpt gen_tac >> strip_tac >>
  `0 <= ll - mm` by
     (CCONTR_TAC >>
      `0 < -(dd * (ll - mm))` by
         (rewrite_tac[GSYM REAL_MUL_RNEG] >>
          MATCH_MP_TAC REAL_LT_MUL >> conj_tac >- first_assum ACCEPT_TAC >>
          pop_assum mp_tac >> REAL_ARITH_TAC) >>
      qpat_x_assum `qq = _` (fn th => pop_assum (mp_tac o REWRITE_RULE [GSYM th])) >>
      qpat_x_assum `pp = _` mp_tac >> qpat_x_assum `0 <= pp` mp_tac >> REAL_ARITH_TAC) >>
  conj_tac
  >- (qpat_x_assum `0 <= ll - mm` mp_tac >> qpat_x_assum `0 <= mm` mp_tac >> REAL_ARITH_TAC) >>
  strip_tac >>
  `ll - mm = 0` by
     (qpat_x_assum `0 <= ll - mm` mp_tac >> qpat_x_assum `0 <= mm` mp_tac >>
      qpat_x_assum `ll = 0` mp_tac >> REAL_ARITH_TAC) >>
  qpat_x_assum `pp = _` SUBST1_TAC >> qpat_x_assum `qq = _` SUBST1_TAC >>
  qpat_x_assum `ll - mm = 0` SUBST1_TAC >>
  FIRST [rewrite_tac[REAL_MUL_RZERO] >> NO_TAC, REAL_ARITH_TAC]
QED

Theorem S049_as_constants[local]:
  S078 /\ S046 /\ S105 /\ S109 /\ S058 /\ S115 ==> S049
Proof
  strip_tac >> rewrite_tac[S049_def] >> rpt gen_tac >>
  rewrite_tac[inner_check_def, LET_THM] >> BETA_TAC >> strip_tac >>
  gen_tac >> strip_tac >>
  (* facts about the region *)
  `LENGTH y = LENGTH grid - 1` by
     (qpat_assum `in_box _ y` (fn th => ACCEPT_TAC (CONJUNCT1 (REWRITE_RULE [in_box_def] th)))) >>
  `LENGTH (widths grid) = LENGTH grid - 1` by ACCEPT_TAC (SPEC ``grid:num list`` S078_th) >>
  `0 <= mval grid y` by (irule S115_th >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  (* S105: the inner polynomial *)
  mp_tac (spec_names [("n", ``LENGTH (grid:num list) - 1``), ("ws", ``widths grid``),
                      ("m", ``mval grid y``), ("rin", ``qv rp rq``)] S105_th) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  `0 <= mults_val (ldot (widths grid) y / 1096) (qv rp rq) lam nu (qv kp kq) nn cc y` by
     (qpat_x_assum `in_box _ _ /\ _ ==> _` mp_tac >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      rewrite_tac[mval_def]) >>
  (* name the components of the state *)
  qspec_then `inner_poly D (LENGTH grid - 1) ab cuts full rp rq lam nu kp kq nn cc`
    strip_assume_tac tuple7 >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  first_x_assum (fn th =>
     if can (find_term (fn t => is_const t andalso fst (dest_const t) = "all_zero")) (concl th)
     then strip_assume_tac (SIMP_RULE (srw_ss()) [] th) else NO_TAC) >>
  qpat_assum `st_wf _ _` (strip_assume_tac o SIMP_RULE (srw_ss()) [st_wf_def]) >>
  (* the linear part vanishes: st_val = the quadratic part Q *)
  `ldot (lin mL (widths grid) g) y = ldot g y + real_of_int mL * ldot (widths grid) y` by
     (irule (GEN_ALL (CONJUNCT1 (SPEC_ALL S058_th))) >>
      FIRST [asm_rewrite_tac[] >> NO_TAC, simp[] >> NO_TAC]) >>
  `ldot (lin mL (widths grid) g) y = 0` by
     (irule (GEN_ALL (CONJUNCT2 (SPEC_ALL S058_th))) >> first_assum ACCEPT_TAC) >>
  `st_val (widths grid) (ok,k,g,Cm,mL,mY,mM) y =
   qform Cm y y + ldot mY y * ldot (widths grid) y +
   real_of_int mM * (ldot (widths grid) y * ldot (widths grid) y)` by
     (simp_tac (srw_ss()) [st_val_def] >> qpat_x_assum `k = 0` SUBST1_TAC >>
      qpat_x_assum `ldot (lin _ _ _) y = 0` mp_tac >>
      qpat_x_assum `ldot (lin _ _ _) y = _ + _` mp_tac >>
      rewrite_tac[real_of_int_num] >> REAL_ARITH_TAC) >>
  (* S109: the matrix *)
  mp_tac (spec_names [("n", ``LENGTH (grid:num list) - 1``), ("ws", ``widths grid``)] S109_th) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  (* S046: strict dominance *)
  mp_tac (spec_names [("c1", ``&(4 ** T2):int``), ("c2", ``&(2 * D):int``),
                      ("M", ``inner_matrix (widths grid) (ok,k,g,Cm,mL,mY,mM)``)] S046_th) >>
  impl_tac
  >- (qpat_assum `LENGTH (inner_matrix _ _) = _` (fn th => rewrite_tac[th]) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      FIRST [simp[] >> NO_TAC, simp[ZERO_LT_EXP, INT_LE, INT_LT] >> NO_TAC,
             rewrite_tac[INT_LT, INT_LE] >> simp[] >> NO_TAC, intLib.ARITH_TAC]) >>
  disch_then (qspec_then `y` mp_tac) >>
  impl_tac
  >- (qpat_assum `LENGTH (inner_matrix _ _) = _` (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  (* the real arithmetic *)
  qspecl_then [`&D`, `L0 ab cuts full y`,
               `mults_val (ldot (widths grid) y / 1096) (qv rp rq) lam nu (qv kp kq) nn cc y`,
               `st_val (widths grid) (ok,k,g,Cm,mL,mY,mM) y`,
               `qform (inner_matrix (widths grid) (ok,k,g,Cm,mL,mY,mM)) y y`] mp_tac final_real >>
  impl_tac
  >- (rpt conj_tac
      >- (qpat_x_assum `0 < D` mp_tac >> simp[])
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- (qpat_assum `qform (inner_matrix _ _) y y = _` SUBST1_TAC >>
          qpat_assum `st_val (widths grid) (ok,k,g,Cm,mL,mY,mM) y = _ + _` SUBST1_TAC >>
          FIRST [REFL_TAC, REAL_ARITH_TAC])
      >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  strip_tac >>
  `qform (inner_matrix (widths grid) (ok,k,g,Cm,mL,mY,mM)) y y = 0` by
     (qpat_x_assum `L0 _ _ _ _ = 0 ==> _` irule >> first_assum ACCEPT_TAC) >>
  rewrite_tac[EVERY_NOT_EXISTS] >> BETA_TAC >> strip_tac >>
  `0 < qform (inner_matrix (widths grid) (ok,k,g,Cm,mL,mY,mM)) y y` by
     (qpat_x_assum `EXISTS _ y ==> _` irule >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `qform _ y y = 0` (fn th => pop_assum (mp_tac o REWRITE_RULE [th])) >>
  FIRST [rewrite_tac[REAL_LT_REFL] >> NO_TAC, REAL_ARITH_TAC]
QED

Theorem S049 = CONV_RULE (RAND_CONV (REWR_CONV S049_def)) S049_as_constants
