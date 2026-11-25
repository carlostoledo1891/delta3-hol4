Theory attempt
Ancestors
  arithmetic list integer real intreal delta3_check delta3_check2 delta3_sem delta3_stmts
Libs
  intLib realLib RealField

fun instance def env =
  let val th = EQ_MP def (ASSUME (lhs (concl def)))
      val vs = fst (strip_forall (concl th))
      fun arg v = let val nm = fst (dest_var v) in
        case List.find (fn (k,_) => k = nm) env of
          SOME (_,q) => q | NONE => [QUOTE nm]
        end
  in Q.SPECL (map arg vs) th end;

val al_spec = SPEC_ALL (EQ_MP S041_def (ASSUME ``S041``));
val al_len = GEN_ALL (CONJUNCT1 al_spec);
val al_dot = GEN_ALL (CONJUNCT2 al_spec);

Theorem matrix_len[local]:
  S041 ==> !rs idx. LENGTH (addm idx j v rs) = LENGTH rs
Proof
  disch_tac >> Induct
  >- simp[addm_def] >>
  qx_genl_tac [`r`,`idx`] >> Cases_on `idx` >> simp[addm_def,al_len]
QED

Theorem matrix_shape[local]:
  S041 ==> !rs idx. EVERY (\r. LENGTH r = n) rs ==>
                    EVERY (\r. LENGTH r = n) (addm idx j v rs)
Proof
  disch_tac >> Induct
  >- simp[addm_def] >>
  qx_genl_tac [`r`,`idx`] >> Cases_on `idx` >> simp[addm_def,al_len]
QED

Theorem matrix_dot[local]:
  S041 ==> !rs idx us. idx < LENGTH rs /\ j < n /\ EVERY (\r. LENGTH r = n) rs /\
     LENGTH us = LENGTH rs /\ LENGTH y = n ==>
     qform (addm idx j v rs) us y = qform rs us y + real_of_int v * (EL idx us * EL j y)
Proof
  disch_tac >> Induct
  >- simp[] >>
  qx_genl_tac [`r`,`idx`,`us`] >>
  namedCases_on `us` ["","x xs"] >- simp[] >>
  namedCases_on `idx` ["","ix"]
  >- (simp_tac (srw_ss()) [addm_def,qform_def] >> strip_tac >>
      `ldot (addl j v r) y = ldot r y + real_of_int v * EL j y` by metis_tac[al_dot] >>
      asm_rewrite_tac[] >> RealField.REAL_ARITH_TAC) >>
  simp_tac (srw_ss()) [addm_def,qform_def] >> strip_tac >>
  `qform (addm ix j v rs) xs y = qform rs xs y + real_of_int v * (EL ix xs * EL j y)`
    by (goalStack.print_tac "tail" >> metis_tac[]) >>
  asm_rewrite_tac[] >> RealField.REAL_ARITH_TAC
QED

Theorem S021_as_constants[local]:
  S041 ==> S021
Proof
  rewrite_tac[S021_def] >> metis_tac[matrix_len,matrix_shape,matrix_dot]
QED

Theorem S021 = CONV_RULE (RAND_CONV (REWR_CONV S021_def)) S021_as_constants
