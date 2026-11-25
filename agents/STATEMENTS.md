# The statements

Each is a boolean constant `Snn` of `delta3_stmtsTheory` (`Snn_def` unfolds it). Free variables are universally closed.
To submit `Snn`, prove the theorem named `Snn` whose conclusion is exactly `Sd1 /\ ... /\ Sdk ==> <statement>` for the listed "may use"
constants in the listed order (just `<statement>` when the list is empty), or refute it (agents/BRIEF.md).
Some statements are false. Some statements share a text and differ only in what they may use.

## S001  [SLAB]

For: the cut pairs enter exactly as theta*bound1 + (1-theta)*bound2, and every theta is in [0,1].

May use: S110, S042

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cut D n (1096 * 1096) zs st) ==> FST st /\ st_wf n (add_cut D n (1096 * 1096) zs st) /\ st_val ws (add_cut D n (1096 * 1096) zs st) y = st_val ws st y + &D * cut_val zs y /\ EVERY (\z. 0 <= FST (SND z) /\ FST (SND z) <= &(SND (SND z))) zs
```

## S002  [INNER]

For: the lam terms lam_ij y_i (1 - y_j) are subtracted exactly and are >= 0 on the box.

May use: S110, S042

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_lam D n lam st) ==> FST st /\ st_wf n (add_lam D n lam st) /\ st_val ws (add_lam D n lam st) y = st_val ws st y - &D * lam_val lam y /\ (in_box n y ==> 0 <= lam_val lam y)
```

## S003  [INNER]

For: the linear terms c_i y_i are subtracted exactly and are >= 0 on the box.

May use: S161, S137

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cc D n i cc st) ==> FST st /\ st_wf n (add_cc D n i cc st) /\ st_val ws (add_cc D n i cc st) y = st_val ws st y - &D * cc_val (i + 1) cc y /\ (in_box n y ==> 0 <= cc_val i cc y)
```

## S004  [INNER]

For: the matrix 2DP is n x n, symmetric, and y^T (2DP) y is twice the quadratic part of the state.

May use: S159, S088

```
st_wf n (ok,k,g,Cm,mL,mY,mM) /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> LENGTH (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) = n /\ EVERY (\r. LENGTH r = n) (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) /\ (!i j. i < n /\ j < n ==> EL j (EL i (inner_matrix ws (ok,k,g,Cm,mL,mY,mM))) = EL i (EL j (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)))) /\ qform (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) y y = 2 * (qform Cm y y + ldot mY y * ldot ws y + real_of_int mM * (ldot ws y * ldot ws y))
```

## S005  [SLAB]

For: the empty state is well-formed, ok, and stands for the zero polynomial.

May use: (nothing)

```
st_wf n (st0 n) /\ FST (st0 n) /\ (LENGTH (y:real list) = n ==> st_val ws (st0 n) y = 0)
```

## S006  [SLAB]

For: forms in m (kinds 7-13) subtract exactly mu * f(y), with m = (SUM W y)/1096, lo = lp/lq, hi = hp/hq.

May use: S083, S145

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ 7 <= kind /\ kind <= 13 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) kind i j k s1 s2 s3 y
```

## S007  [INNER]

For: the kap term kap m (rin - m) is subtracted exactly, kap >= 0.

May use: S161, S137

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_kap D n 1096 rp rq kp kq st) ==> FST st /\ 0 < kp /\ st_wf n (add_kap D n 1096 rp rq kp kq st) /\ st_val ws (add_kap D n 1096 rp rq kp kq st) y = st_val ws st y - &D * qv kp kq * ((ldot ws y / 1096) * (qv rp rq - ldot ws y / 1096))
```

## S008  [SLAB]

For: an accepted form has a non-negative multiplier, a known kind, indices in range, and a legal triangle sign pattern.

May use: S135

```
FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> FST st /\ 0 < mp /\ kind <= 14 /\ form_idx_ok n kind i j k /\ (kind = 14 ==> (s1 = 1 \/ s1 = -1) /\ (s2 = 1 \/ s2 = -1) /\ (s3 = 1 \/ s3 = -1) /\ s1 * s2 * s3 = 1)
```

## S009  [SLAB]

For: the triangle form (kind 14) subtracts exactly mu * (1 + s1 z_i z_j + s2 z_j z_k + s3 z_i z_k).

May use: S135, S138, S082

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ kind = 14 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i k j s1 s2 s3 y
```

## S010  [INNER]

For: the lam terms lam_ij y_i (1 - y_j) are subtracted exactly and are >= 0 on the box.

May use: S083, S145

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_lam D n lam st) ==> FST st /\ st_wf n (add_lam D n lam st) /\ st_val ws (add_lam D n lam st) y = st_val ws st y - &D * lam_val lam y /\ 0 <= lam_val lam y
```

## S011  [SLAB]

For: the accepted forms sum to something non-negative on the region.

May use: S157, S062, S141

```
FST (add_forms D n 1096 lp lq hp hq forms st) /\ in_box n y /\ lo <= m /\ m <= hi ==> 0 <= forms_val m lo hi forms y
```

## S012  [SLAB]

For: the cut pairs enter exactly as theta*bound1 + (1-theta)*bound2, and every theta is in [0,1].

May use: S083, S145

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cut D n (1096 * 1096) zs st) ==> FST st /\ st_wf n (add_cut D n (1096 * 1096) zs st) /\ st_val ws (add_cut D n (1096 * 1096) zs st) y = st_val ws st y + &D * cut_val zs y /\ EVERY (\z. 0 <= FST (SND z) /\ FST (SND z) < &(SND (SND z))) zs
```

## S013  [INNER]

For: m >= 0 on the box when the grid increases.

May use: S150

```
in_box (LENGTH grid - 1) y ==> 0 <= mval grid y
```

## S014  [SLAB]

For: v^T M v at v = (1, y) is 2 * (the state polynomial) + 2 D eps |v|^2.

May use: S159, S088

```
st_wf n st /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> qform (slab_matrix D ep eq ws st) (1 :: y) (1 :: y) = 2 * st_val ws st y + 2 * real_of_int (sc D ep eq) * sumsq y
```

## S015  [INNER]

For: TOP (inner): if the check returns T then L0 >= 0 on the region, with equality only at y = 0.

May use: S078, S046, S028, S050, S058, S115

```
inner_check ab cuts full grid rp rq lam nu kp kq nn cc D T2 ds Lw ==> !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv rp rq ==> 0 < L0 ab cuts full y /\ (L0 ab cuts full y = 0 ==> EVERY (\x. x = 0) y)
```

## S016  [SLAB]

For: the matrix M = 2D(S + eps I) is (n+1) x (n+1) and symmetric.

May use: S159, S088

```
st_wf n st /\ LENGTH (ws:int list) = n ==> LENGTH (slab_matrix D ep eq ws st) = n /\ EVERY (\r. LENGTH r = n + 1) (slab_matrix D ep eq ws st) /\ !i j. i < n + 1 /\ j < n + 1 ==> EL j (EL i (slab_matrix D ep eq ws st)) = EL i (EL j (slab_matrix D ep eq ws st))
```

## S017  [SLAB]

For: the integer p * (D DIV q) is exactly D * p/q when q divides D.

May use: (nothing)

```
0 < D /\ D MOD q = 0 ==> real_of_int (sc D p q) = &D * qv p q
```

## S018  [SLAB]

For: the full pairs enter exactly.

May use: S161, S137

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_full D n (1096 * 1096) full st) ==> FST st /\ st_wf n (add_full D n (1096 * 1096) full st) /\ st_val ws (add_full D n (1096 * 1096) full st) y = st_val ws st y + &D * full_val full y
```

## S019  [SLAB]

For: the rebuilt slab polynomial is D * (L_theta - B - SUM mu_f f).

May use: S110, S042, S005, S130, S100, S001, S146

```
0 < D /\ LENGTH (y:real list) = n /\ FST (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) ==> st_wf n (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) /\ D MOD Bq = 0 /\ st_val ws (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) y = &D * (Ltheta ab cuts full theta y - qv Bp Bq - forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y)
```

## S020  [INNER]

For: the nu terms nu_j y_j (rin - m) are subtracted exactly and are >= 0 on the region.

May use: S161, S145

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nu D n 1096 rp rq j nu st) ==> FST st /\ st_wf n (add_nu D n 1096 rp rq j nu st) /\ st_val ws (add_nu D n 1096 rp rq j nu st) y = st_val ws st y - &D * nu_val (ldot ws y / 1096) (qv rp rq) j nu y /\ (in_box n y ==> 0 <= nu_val m rin j nu y)
```

## S021  [SLAB]

For: adding v at (i, j) of a matrix adds v * u_i * y_j to its bilinear form, shape kept.

May use: S041

```
LENGTH (addm i j v Cm) = LENGTH Cm /\ (EVERY (\r. LENGTH r = n) Cm ==> EVERY (\r. LENGTH r = n) (addm i j v Cm)) /\ (i < LENGTH Cm /\ j < n /\ EVERY (\r. LENGTH r = n) Cm /\ LENGTH (u:real list) = LENGTH Cm /\ LENGTH (y:real list) = n ==> qform (addm i j v Cm) u y = qform Cm u y + real_of_int v * (EL i u * EL j y))
```

## S022  [SLAB]

For: the full pairs enter exactly.

May use: S135, S137

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_full D n (1096 * 1096) full st) ==> FST st /\ st_wf n (add_full D n (1096 * 1096) full st) /\ st_val ws (add_full D n (1096 * 1096) full st) y = st_val ws st y + &D * full_val full y
```

## S023  [INNER]

For: y^T N y (upper triangle given) is subtracted exactly and is >= 0 on the box.

May use: S083, S145

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nn D n nn st) ==> FST st /\ st_wf n (add_nn D n nn st) /\ st_val ws (add_nn D n nn st) y = st_val ws st y - &D * (2 * nn_val nn y) /\ (in_box n y ==> 0 <= nn_val nn y)
```

## S024  [SLAB]

For: the integer test claim <= B - eps(1+n) means what it says in rationals.

May use: (nothing)

```
0 < Bq /\ 0 < eq /\ (cp:int) * &(Bq:num) * &(eq:num) <= (Bp * &eq - ep * &(n + 1) * &Bq) * &(cq:num) ==> qv cp cq <= qv Bp Bq - qv ep eq * &(n + 1)
```

## S025  [SLAB]

For: |y|^2 <= n on the box.

May use: (nothing)

```
in_box n y ==> sumsq y < &n
```

## S026  [INNER]

For: y^T N y (upper triangle given) is subtracted exactly and is >= 0 on the box.

May use: S083, S138

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nn D n nn st) ==> FST st /\ st_wf n (add_nn D n nn st) /\ st_val ws (add_nn D n nn st) y = st_val ws st y - &D * nn_val nn y /\ (in_box n y ==> 0 <= nn_val nn y)
```

## S027  [SLAB]

For: the matrix M = 2D(S + eps I) is (n+1) x (n+1) and symmetric.

May use: S052, S038

```
st_wf n st /\ LENGTH (ws:int list) = n ==> LENGTH (slab_matrix D ep eq ws st) = n + 1 /\ EVERY (\r. LENGTH r = n + 1) (slab_matrix D ep eq ws st) /\ !i j. i < n + 1 /\ j < n + 1 ==> EL j (EL i (slab_matrix D ep eq ws st)) = EL i (EL j (slab_matrix D ep eq ws st))
```

## S028  [INNER]

For: the rebuilt inner polynomial is D * (L0 - every multiplier term), and the multiplier terms are >= 0 on the region.

May use: S153, S092, S158, S029, S056, S069, S035, S031, S075

```
0 < D /\ LENGTH (y:real list) = n /\ FST (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) ==> st_wf n (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) /\ st_val ws (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) y = &D * (L0 ab cuts full y - mults_val (ldot ws y / 1096) (qv rp rq) lam nu (qv kp kq) nn cc y) /\ (in_box n y /\ 0 <= m /\ m <= rin ==> 0 <= mults_val m rin lam nu (qv kp kq) nn cc y)
```

## S029  [INNER]

For: the cut pairs of L0 (the bound that vanishes at 0) enter exactly.

May use: S135, S137

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cut0 D n (1096 * 1096) cuts st) ==> FST st /\ st_wf n (add_cut0 D n (1096 * 1096) cuts st) /\ st_val ws (add_cut0 D n (1096 * 1096) cuts st) y = st_val ws st y + &D * cut0_val cuts y
```

## S030  [INNER]

For: the linear terms c_i y_i are subtracted exactly and are >= 0 on the box.

May use: S135, S137

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cc D n i cc st) ==> FST st /\ st_wf n (add_cc D n i cc st) /\ st_val ws (add_cc D n i cc st) y = st_val ws st y - &D * cc_val i cc y /\ (in_box n y ==> 0 <= cc_val i cc y)
```

## S031  [INNER]

For: y^T N y (upper triangle given) is subtracted exactly and is >= 0 on the box.

May use: S135, S137

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nn D n nn st) ==> FST st /\ st_wf n (add_nn D n nn st) /\ st_val ws (add_nn D n nn st) y = st_val ws st y - &D * nn_val nn y /\ (in_box n y ==> 0 <= nn_val nn y)
```

## S032  [SLAB]

For: forms in the y's alone (kinds 0-6) subtract exactly mu * f(y).

May use: S161, S137

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ kind <= 7 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i j k s1 s2 s3 y
```

## S033  [SLAB]

For: the per-cell terms a_i y_i + b_i y_i^2 enter exactly.

May use: S083, S072

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cells D n i ab st) ==> FST st /\ st_wf n (add_cells D n i ab st) /\ st_val ws (add_cells D n i ab st) y = st_val ws st y + &D * cells_val (i + 1) ab y
```

## S034  [SLAB]

For: CRITICAL PATH: weighted diagonal dominance of 4^T M - 2D Lw Lw^T makes v^T M v >= 0.

May use: (nothing)

```
dd_rows c1 c2 0 M Lw Lw ds ds /\ LENGTH Lw = LENGTH M /\ LENGTH ds = LENGTH M /\ EVERY (\r. LENGTH r = LENGTH M) M /\ (!i j. i < LENGTH M /\ j < LENGTH M ==> EL j (EL i M) = EL i (EL j M)) /\ 0 <= c2 ==> !v:real list. LENGTH v = LENGTH M ==> 0 <= qform M v v
```

## S035  [INNER]

For: the kap term kap m (rin - m) is subtracted exactly, kap >= 0.

May use: S161, S138

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_kap D n 1096 rp rq kp kq st) ==> FST st /\ 0 < kp /\ st_wf n (add_kap D n 1096 rp rq kp kq st) /\ st_val ws (add_kap D n 1096 rp rq kp kq st) y = st_val ws st y - &D * qv kp kq * ((ldot ws y / 1096) * (qv rp rq - ldot ws y / 1096))
```

## S036  [INNER]

For: the rebuilt inner polynomial is D * (L0 - every multiplier term), and the multiplier terms are >= 0 on the region.

May use: S005, S092, S018, S142, S055, S128, S076, S023, S030

```
0 < D /\ LENGTH (y:real list) = n /\ FST (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) ==> st_wf n (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) /\ st_val ws (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) y = &D * (L0 ab cuts full y + mults_val (ldot ws y / 1096) (qv rp rq) lam nu (qv kp kq) nn cc y) /\ (in_box n y /\ 0 <= m /\ m <= rin ==> 0 <= mults_val m rin lam nu (qv kp kq) nn cc y)
```

## S037  [SLAB]

For: the whole list of forms subtracts exactly SUM mu_f f(y).

May use: S008, S151, S112, S101

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_forms D n 1096 lp lq hp hq forms st) ==> FST st /\ st_wf n (add_forms D n 1096 lp lq hp hq forms st) /\ st_val ws (add_forms D n 1096 lp lq hp hq forms st) y = st_val ws st y + &D * forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y
```

## S038  [SLAB]

For: lin c ws g is g + c * ws entrywise.

May use: (nothing)

```
LENGTH (ws:int list) = LENGTH g ==> LENGTH (lin c ws g) = LENGTH g /\ !i. i < LENGTH g ==> EL i (lin c ws g) = EL i g + c * EL i ws
```

## S039  [INNER]

For: the rebuilt inner polynomial is D * (L0 - every multiplier term), and the multiplier terms are >= 0 on the region.

May use: S153, S085, S158, S066, S010, S119, S007, S026, S003

```
0 < D /\ LENGTH (y:real list) = n /\ FST (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) ==> st_wf n (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) /\ st_val ws (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) y = &D * (L0 ab cuts full y - mults_val (ldot ws y / 1096) (qv rp rq) lam nu (qv kp kq) nn cc y) /\ (in_box n y /\ 0 <= m /\ m <= rin ==> 0 <= mults_val m rin lam nu (qv kp kq) nn cc y)
```

## S040  [SLAB]

For: CRITICAL PATH: weighted diagonal dominance of 4^T M - 2D Lw Lw^T makes v^T M v >= 0.

May use: (nothing)

```
dd_rows c1 c2 0 M Lw Lw ds ds /\ LENGTH Lw = LENGTH M /\ LENGTH ds = LENGTH M /\ EVERY (\r. LENGTH r = LENGTH M) M /\ (!i j. i < LENGTH M /\ j < LENGTH M ==> EL j (EL i M) = EL i (EL j M)) /\ 0 < c1 /\ 0 <= c2 ==> !v:real list. LENGTH v = LENGTH M ==> 0 <= qform M v v
```

## S041  [SLAB]

For: adding v at position n of a list adds v * y_n to its dot product.

May use: (nothing)

```
LENGTH (addl n v l) = LENGTH l /\ (n < LENGTH l /\ LENGTH (y:real list) = LENGTH l ==> ldot (addl n v l) y = ldot l y + real_of_int v * EL n y)
```

## S042  [SLAB]

For: one accepted term adds exactly D * (p/q) * its monomial.

May use: S017, S041, S021, S110

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_term D n tag i j p q st) ==> st_val ws (add_term D n tag i j p q st) y = st_val ws st y + &D * qv p q * mono ws tag i j y
```

## S043  [INNER]

For: the kap term kap m (rin - m) is subtracted exactly, kap >= 0.

May use: S110, S042

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_kap D n 1096 rp rq kp kq st) ==> FST st /\ 0 <= kp /\ st_wf n (add_kap D n 1096 rp rq kp kq st) /\ st_val ws (add_kap D n 1096 rp rq kp kq st) y = st_val ws st y - &D * qv kp kq * ((ldot ws y / 1096) * (qv rp rq - ldot ws y / 1096))
```

## S044  [SLAB]

For: forms in the y's alone (kinds 0-6) subtract exactly mu * f(y).

May use: S135, S072

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ kind <= 7 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i j k s1 s2 s3 y
```

## S045  [SLAB]

For: TOP (slabs): if the check returns T then L_theta >= the claim everywhere on the region.

May use: S131, S074, S132, S125, S014, S025, S150, S034, S024

```
slab_check ab cuts full grid lp lq hp hq Bp Bq ep eq cp cq theta forms D T2 ds Lw ==> !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv hp hq ==> qv cp cq <= Ltheta ab cuts full theta y
```

## S046  [STRICT]

For: strict weighted dominance makes v^T M v > 0 for v <> 0 (strictness without leading minors).

May use: S040

```
sdd_rows c1 c2 0 M Lw Lw ds ds /\ LENGTH Lw = LENGTH M /\ LENGTH ds = LENGTH M /\ EVERY (\r. LENGTH r = LENGTH M) M /\ (!i j. i < LENGTH M /\ j < LENGTH M ==> EL j (EL i M) = EL i (EL j M)) /\ 0 < c1 /\ 0 <= c2 ==> !v:real list. LENGTH v = LENGTH M ==> 0 <= qform M v v /\ (EXISTS (\x. x <> 0) v ==> 0 < qform M v v)
```

## S047  [INNER]

For: the linear terms c_i y_i are subtracted exactly and are >= 0 on the box.

May use: S110, S042

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cc D n i cc st) ==> FST st /\ st_wf n (add_cc D n i cc st) /\ st_val ws (add_cc D n i cc st) y = st_val ws st y - &D * cc_val i cc y /\ (in_box n y ==> 0 <= cc_val i cc y)
```

## S048  [INNER]

For: the cut pairs of L0 (the bound that vanishes at 0) enter exactly.

May use: S110, S042

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cut0 D n (1096 * 1096) cuts st) ==> FST st /\ st_wf n (add_cut0 D n (1096 * 1096) cuts st) /\ st_val ws (add_cut0 D n (1096 * 1096) cuts st) y = st_val ws st y + &D * cut0_val cuts y
```

## S049  [INNER]

For: TOP (inner): if the check returns T then L0 >= 0 on the region, with equality only at y = 0.

May use: S078, S046, S105, S109, S058, S115

```
inner_check ab cuts full grid rp rq lam nu kp kq nn cc D T2 ds Lw ==> !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv rp rq ==> 0 <= L0 ab cuts full y /\ (L0 ab cuts full y = 0 ==> EVERY (\x. x = 0) y)
```

## S050  [INNER]

For: the matrix 2DP is n x n, symmetric, and y^T (2DP) y is twice the quadratic part of the state.

May use: S159, S088

```
st_wf n (ok,k,g,Cm,mL,mY,mM) /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> LENGTH (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) = n /\ EVERY (\r. LENGTH r = n) (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) /\ (!i j. i < n /\ j < n ==> EL j (EL i (inner_matrix ws (ok,k,g,Cm,mL,mY,mM))) = EL i (EL j (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)))) /\ qform (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) y y = (qform Cm y y + ldot mY y * ldot ws y + real_of_int mM * (ldot ws y * ldot ws y))
```

## S051  [SLAB]

For: the triangle form (kind 14) subtracts exactly mu * (1 + s1 z_i z_j + s2 z_j z_k + s3 z_i z_k).

May use: S135, S137, S155

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ kind = 14 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i j k s1 s2 s3 y
```

## S052  [SLAB]

For: transp is the transpose.

May use: (nothing)

```
EVERY (\r. LENGTH r = n) (Cm:int list list) ==> LENGTH (transp n Cm) = n /\ EVERY (\r. LENGTH r = LENGTH Cm) (transp n Cm) /\ !i j. i < n /\ j < LENGTH Cm ==> EL j (EL i (transp n Cm)) = EL i (EL j Cm)
```

## S053  [COVER]

For: cover a ivs: every m with a < m <= 1/2 lies in one of the intervals.

May use: (nothing)

```
cover ap aq ivs ==> !m:real. qv ap aq < m /\ m <= 1 / 2 ==> in_some m ivs
```

## S054  [SLAB]

For: the triangle inequality 1 + s1 ab + s2 bc + s3 ac >= 0 on the cube when s1 s2 s3 = 1.

May use: (nothing)

```
-1 <= a /\ a <= 1 /\ -1 <= b /\ b <= 1 /\ -1 <= c /\ c <= (1:real) /\ (s1 = 1 \/ s1 = -1) /\ (s2 = 1 \/ s2 = -1) /\ (s3 = 1 \/ s3 = -1) /\ s1 * s2 * s3 = (1:int) ==> 0 <= 1 + real_of_int s1 * (a * b) + real_of_int s2 * (b * c) + real_of_int s3 * (a * c)
```

## S055  [INNER]

For: the lam terms lam_ij y_i (1 - y_j) are subtracted exactly and are >= 0 on the box.

May use: S135, S137

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_lam D n lam st) ==> FST st /\ st_wf n (add_lam D n lam st) /\ st_val ws (add_lam D n lam st) y = st_val ws st y - &D * lam_val lam y /\ (in_box n y ==> 0 <= lam_val lam y)
```

## S056  [INNER]

For: the lam terms lam_ij y_i (1 - y_j) are subtracted exactly and are >= 0 on the box.

May use: S161, S137

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_lam D n lam st) ==> FST st /\ st_wf n (add_lam D n lam st) /\ st_val ws (add_lam D n lam st) y = st_val ws st y - &D * lam_val lam y /\ (in_box n y ==> 0 <= lam_val lam y)
```

## S057  [SLAB]

For: v^T M v at v = (1, y) is 2 * (the state polynomial) + 2 D eps |v|^2.

May use: S052, S038

```
st_wf n st /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> qform (slab_matrix D ep eq ws st) (1 :: y) (1 :: y) = 2 * st_val ws st y + 2 * real_of_int (sc D ep eq) * (1 + sumsq y)
```

## S058  [INNER]

For: the linear part after expanding m, and: an all-zero list has dot product 0.

May use: S038

```
(LENGTH (ws:int list) = LENGTH g /\ LENGTH (y:real list) = LENGTH g ==> ldot (lin mL ws g) y = ldot g y + real_of_int mL * ldot ws y) /\ (all_zero l ==> ldot l y = 0)
```

## S059  [INNER]

For: the nu terms nu_j y_j (rin - m) are subtracted exactly and are >= 0 on the region.

May use: S110, S042

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nu D n 1096 rp rq j nu st) ==> FST st /\ st_wf n (add_nu D n 1096 rp rq j nu st) /\ st_val ws (add_nu D n 1096 rp rq j nu st) y = st_val ws st y - &D * nu_val (ldot ws y / 1096) (qv rp rq) j nu y /\ (in_box n y /\ m <= rin ==> 0 <= nu_val m rin j nu y)
```

## S060  [INNER]

For: m >= 0 on the box when the grid increases.

May use: S078

```
in_box (LENGTH grid - 1) y ==> 0 <= mval grid y
```

## S061  [SLAB]

For: adding v at position n of a list adds v * y_n to its dot product.

May use: (nothing)

```
LENGTH (addl n v l) = LENGTH l /\ (n < LENGTH l /\ LENGTH (y:real list) = LENGTH l ==> ldot (addl n v l) y = ldot l y + 2 * real_of_int v * EL n y)
```

## S062  [SLAB]

For: every non-triangle form is non-negative on the region.

May use: (nothing)

```
in_box n y /\ m <= hi /\ kind <= 13 /\ form_idx_ok n kind i j k ==> 0 <= form_val m lo hi kind i j k s1 s2 s3 y
```

## S063  [SLAB]

For: TOP (slabs): if the check returns T then L_theta >= the claim everywhere on the region.

May use: S131, S011, S116, S070, S136, S025, S150, S034, S024

```
slab_check ab cuts full grid lp lq hp hq Bp Bq ep eq cp cq theta forms D T2 ds Lw ==> !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv hp hq ==> qv cp cq <= Ltheta ab cuts full theta y
```

## S064  [SLAB]

For: the triangle form (kind 14) subtracts exactly mu * (1 + s1 z_i z_j + s2 z_j z_k + s3 z_i z_k).

May use: S161, S138, S077

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ kind = 14 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i k j s1 s2 s3 y
```

## S065  [INNER]

For: the linear part after expanding m, and: an all-zero list has dot product 0.

May use: S038

```
(LENGTH (ws:int list) = LENGTH g /\ LENGTH (y:real list) = LENGTH g ==> ldot (lin mL ws g) y = ldot g y - real_of_int mL * ldot ws y) /\ (all_zero l ==> ldot l y = 0)
```

## S066  [INNER]

For: the cut pairs of L0 (the bound that vanishes at 0) enter exactly.

May use: S161, S072

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cut0 D n (1096 * 1096) cuts st) ==> FST st /\ st_wf n (add_cut0 D n (1096 * 1096) cuts st) /\ st_val ws (add_cut0 D n (1096 * 1096) cuts st) y = st_val ws st y - &D * cut0_val cuts y
```

## S067  [SLAB]

For: adding v at (i, j) of a matrix adds v * u_i * y_j to its bilinear form, shape kept.

May use: S061

```
LENGTH (addm i j v Cm) = LENGTH Cm /\ (EVERY (\r. LENGTH r = n) Cm ==> EVERY (\r. LENGTH r = n) (addm i j v Cm)) /\ (i < LENGTH Cm /\ j < n /\ EVERY (\r. LENGTH r = n) Cm /\ LENGTH (u:real list) = LENGTH Cm /\ LENGTH (y:real list) = n ==> qform (addm i j v Cm) u y = qform Cm u y + real_of_int v * (EL i u * EL j y))
```

## S068  [SLAB]

For: the accepted forms sum to something non-negative on the region.

May use: S095, S152, S054

```
FST (add_forms D n 1096 lp lq hp hq forms st) /\ LENGTH (y:real list) = n /\ lo <= m /\ m <= hi ==> 0 <= forms_val m lo hi forms y
```

## S069  [INNER]

For: the nu terms nu_j y_j (rin - m) are subtracted exactly and are >= 0 on the region.

May use: S161, S137

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nu D n 1096 rp rq j nu st) ==> FST st /\ st_wf n (add_nu D n 1096 rp rq j nu st) /\ st_val ws (add_nu D n 1096 rp rq j nu st) y = st_val ws st y - &D * nu_val (ldot ws y / 1096) (qv rp rq) j nu y /\ (in_box n y /\ m <= rin ==> 0 <= nu_val m rin j nu y)
```

## S070  [SLAB]

For: the matrix M = 2D(S + eps I) is (n+1) x (n+1) and symmetric.

May use: S052, S088

```
st_wf n st /\ LENGTH (ws:int list) = n ==> LENGTH (slab_matrix D ep eq ws st) = n /\ EVERY (\r. LENGTH r = n + 1) (slab_matrix D ep eq ws st) /\ !i j. i < n + 1 /\ j < n + 1 ==> EL j (EL i (slab_matrix D ep eq ws st)) = EL i (EL j (slab_matrix D ep eq ws st))
```

## S071  [SLAB]

For: the cut pairs enter exactly as theta*bound1 + (1-theta)*bound2, and every theta is in [0,1].

May use: S083, S072

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cut D n (1096 * 1096) zs st) ==> FST st /\ st_wf n (add_cut D n (1096 * 1096) zs st) /\ st_val ws (add_cut D n (1096 * 1096) zs st) y = st_val ws st y + &D * cut_val zs y /\ EVERY (\z. 0 <= FST (SND z) /\ FST (SND z) < &(SND (SND z))) zs
```

## S072  [SLAB]

For: one accepted term adds exactly D * (p/q) * its monomial.

May use: S131, S061, S122, S135

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_term D n tag i j p q st) ==> st_val ws (add_term D n tag i j p q st) y = st_val ws st y + &D * qv p q * mono ws tag i j y
```

## S073  [INNER]

For: TOP (inner): if the check returns T then L0 >= 0 on the region, with equality only at y = 0.

May use: S150, S160, S039, S103, S143, S013

```
inner_check ab cuts full grid rp rq lam nu kp kq nn cc D T2 ds Lw ==> !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv rp rq ==> 0 <= L0 ab cuts full y /\ (L0 ab cuts full y = 0 ==> EVERY (\x. x = 0) y)
```

## S074  [SLAB]

For: the accepted forms sum to something non-negative on the region.

May use: S008, S062, S086

```
FST (add_forms D n 1096 lp lq hp hq forms st) /\ in_box n y /\ lo <= m /\ m <= hi ==> 0 <= forms_val m lo hi forms y
```

## S075  [INNER]

For: the linear terms c_i y_i are subtracted exactly and are >= 0 on the box.

May use: S083, S072

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cc D n i cc st) ==> FST st /\ st_wf n (add_cc D n i cc st) /\ st_val ws (add_cc D n i cc st) y = st_val ws st y - &D * cc_val (i + 1) cc y /\ (in_box n y ==> 0 <= cc_val i cc y)
```

## S076  [INNER]

For: the kap term kap m (rin - m) is subtracted exactly, kap >= 0.

May use: S083, S072

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_kap D n 1096 rp rq kp kq st) ==> FST st /\ 0 < kp /\ st_wf n (add_kap D n 1096 rp rq kp kq st) /\ st_val ws (add_kap D n 1096 rp rq kp kq st) y = st_val ws st y - &D * qv kp kq * ((ldot ws y / 1096) * (qv rp rq - ldot ws y / 1096))
```

## S077  [SLAB]

For: the helper of the triangle form subtracts c/q * z_a z_b, z = 1 - 2y.

May use: S083, S072

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_zz D n c q a b st) ==> FST st /\ st_wf n (add_zz D n c q a b st) /\ st_val ws (add_zz D n c q a b st) y = st_val ws st y - &D * qv c q * ((1 - 2 * EL a y) * (1 - 2 * EL b y))
```

## S078  [SLAB]

For: a grid of n+1 points has n widths.

May use: (nothing)

```
LENGTH (widths grid) = LENGTH grid - 1
```

## S079  [SLAB]

For: the helper of the triangle form subtracts c/q * z_a z_b, z = 1 - 2y.

May use: S083, S145

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_zz D n c q a b st) ==> FST st /\ st_wf n (add_zz D n c q a b st) /\ st_val ws (add_zz D n c q a b st) y = st_val ws st y + &D * qv c q * ((1 - 2 * EL a y) * (1 - 2 * EL b y))
```

## S080  [SLAB]

For: the full pairs enter exactly.

May use: S083, S145

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_full D n 1096 full st) ==> FST st /\ st_wf n (add_full D n 1096 full st) /\ st_val ws (add_full D n 1096 full st) y = st_val ws st y + &D * full_val full y
```

## S081  [INNER]

For: the kap term kap m (rin - m) is subtracted exactly, kap >= 0.

May use: S161, S137

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_kap D n 1096 rp rq kp kq st) ==> FST st /\ 0 <= kp /\ st_wf n (add_kap D n 1096 rp rq kp kq st) /\ st_val ws (add_kap D n 1096 rp rq kp kq st) y = st_val ws st y - &D * qv kp kq * ((ldot ws y / 1096) * (qv rp rq - ldot ws y / 1096))
```

## S082  [SLAB]

For: the helper of the triangle form subtracts c/q * z_a z_b, z = 1 - 2y.

May use: S161, S138

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_zz D n c q a b st) ==> FST st /\ st_wf n (add_zz D n c q a b st) /\ st_val ws (add_zz D n c q a b st) y = st_val ws st y + &D * qv c q * ((1 - 2 * EL a y) * (1 - 2 * EL b y))
```

## S083  [SLAB]

For: add_term keeps the state well-formed, and an ok result means every guard held.

May use: S041, S021

```
(st_wf n st ==> st_wf n (add_term D n tag i j p q st)) /\ (FST (add_term D n tag i j p q st) ==> FST st /\ D MOD q = 0 /\ i < n /\ j < n /\ tag < 5)
```

## S084  [SLAB]

For: forms in the y's alone (kinds 0-6) subtract exactly mu * f(y).

May use: S110, S042

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ kind <= 6 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i j k s1 s2 s3 y
```

## S085  [SLAB]

For: the per-cell terms a_i y_i + b_i y_i^2 enter exactly.

May use: S161, S145

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cells D n i ab st) ==> FST st /\ st_wf n (add_cells D n i ab st) /\ st_val ws (add_cells D n i ab st) y = st_val ws st y + &D * cells_val (i + 1) ab y
```

## S086  [SLAB]

For: the triangle inequality 1 + s1 ab + s2 bc + s3 ac >= 0 on the cube when s1 s2 s3 = 1.

May use: (nothing)

```
-1 <= a /\ a <= 1 /\ -1 <= b /\ b <= 1 /\ -1 <= c /\ c <= (1:real) /\ (s1 = 1 \/ s1 = -1) /\ (s2 = 1 \/ s2 = -1) /\ (s3 = 1 \/ s3 = -1) /\ s1 * s2 * s3 = (1:int) ==> 0 < 1 + real_of_int s1 * (a * b) + real_of_int s2 * (b * c) + real_of_int s3 * (a * c)
```

## S087  [SLAB]

For: TOP (slabs): if the check returns T then L_theta >= the claim everywhere on the region.

May use: S017, S118, S127, S134, S124, S123, S078, S040, S108

```
slab_check ab cuts full grid lp lq hp hq Bp Bq ep eq cp cq theta forms D T2 ds Lw ==> !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv hp hq ==> qv cp cq <= Ltheta ab cuts full theta y
```

## S088  [SLAB]

For: lin c ws g is g + c * ws entrywise.

May use: (nothing)

```
LENGTH (ws:int list) = LENGTH g ==> LENGTH (lin c ws g) = LENGTH g /\ !i. i < LENGTH g ==> EL i (lin c ws g) = EL i g + EL i ws
```

## S089  [SLAB]

For: the triangle form (kind 14) subtracts exactly mu * (1 + s1 z_i z_j + s2 z_j z_k + s3 z_i z_k).

May use: S110, S042, S117

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ kind = 14 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i j k s1 s2 s3 y
```

## S090  [COVER]

For: TOP (cover): the regions cover every m in [0, 1/2].

May use: S102

```
cover_all ivs ==> !m:real. 0 <= m /\ m <= 1 ==> in_some m ivs
```

## S091  [SLAB]

For: the whole list of forms subtracts exactly SUM mu_f f(y).

May use: S095, S032, S006, S009

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_forms D n 1096 lp lq hp hq forms st) ==> FST st /\ st_wf n (add_forms D n 1096 lp lq hp hq forms st) /\ st_val ws (add_forms D n 1096 lp lq hp hq forms st) y = st_val ws st y + &D * forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y
```

## S092  [SLAB]

For: the per-cell terms a_i y_i + b_i y_i^2 enter exactly.

May use: S083, S145

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cells D n i ab st) ==> FST st /\ st_wf n (add_cells D n i ab st) /\ st_val ws (add_cells D n i ab st) y = st_val ws st y + &D * cells_val i ab y
```

## S093  [INNER]

For: TOP (inner): if the check returns T then L0 >= 0 on the region, with equality only at y = 0.

May use: S150, S160, S036, S004, S143, S060

```
inner_check ab cuts full grid rp rq lam nu kp kq nn cc D T2 ds Lw ==> !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv rp rq ==> 0 < L0 ab cuts full y /\ (L0 ab cuts full y = 0 ==> EVERY (\x. x = 0) y)
```

## S094  [SLAB]

For: the per-cell terms a_i y_i + b_i y_i^2 enter exactly.

May use: S083, S138

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cells D n i ab st) ==> FST st /\ st_wf n (add_cells D n i ab st) /\ st_val ws (add_cells D n i ab st) y = st_val ws st y + &D * cells_val i ab y
```

## S095  [SLAB]

For: an accepted form has a non-negative multiplier, a known kind, indices in range, and a legal triangle sign pattern.

May use: S110

```
FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> FST st /\ 0 <= mp /\ kind <= 14 /\ form_idx_ok n kind i j k /\ (kind = 14 ==> (s1 = 1 \/ s1 = -1) /\ (s2 = 1 \/ s2 = -1) /\ (s3 = 1 \/ s3 = -1) /\ s1 * s2 * s3 = 1)
```

## S096  [INNER]

For: the lam terms lam_ij y_i (1 - y_j) are subtracted exactly and are >= 0 on the box.

May use: S161, S072

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_lam D n lam st) ==> FST st /\ st_wf n (add_lam D n lam st) /\ st_val ws (add_lam D n lam st) y = st_val ws st y - &D * lam_val lam y /\ 0 <= lam_val lam y
```

## S097  [SLAB]

For: the whole list of forms subtracts exactly SUM mu_f f(y).

May use: S157, S156, S106, S064

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_forms D n 1096 lp lq hp hq forms st) ==> FST st /\ st_wf n (add_forms D n 1096 lp lq hp hq forms st) /\ st_val ws (add_forms D n 1096 lp lq hp hq forms st) y = st_val ws st y - &D * forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y
```

## S098  [SLAB]

For: forms in m (kinds 7-13) subtract exactly mu * f(y), with m = (SUM W y)/1096, lo = lp/lq, hi = hp/hq.

May use: S110, S042

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ 7 <= kind /\ kind <= 13 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) kind i j k s1 s2 s3 y
```

## S099  [COVER]

For: TOP (cover): the regions cover every m in [0, 1/2].

May use: S053

```
cover_all ivs ==> !m:real. 0 <= m /\ m <= 1 ==> in_some m ivs
```

## S100  [SLAB]

For: the full pairs enter exactly.

May use: S110, S042

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_full D n (1096 * 1096) full st) ==> FST st /\ st_wf n (add_full D n (1096 * 1096) full st) /\ st_val ws (add_full D n (1096 * 1096) full st) y = st_val ws st y + &D * full_val full y
```

## S101  [SLAB]

For: the triangle form (kind 14) subtracts exactly mu * (1 + s1 z_i z_j + s2 z_j z_k + s3 z_i z_k).

May use: S161, S137, S079

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ kind = 14 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i j k s1 s2 s3 y
```

## S102  [COVER]

For: cover a ivs: every m with a < m <= 1/2 lies in one of the intervals.

May use: (nothing)

```
cover ap aq ivs ==> !m:real. qv ap aq <= m /\ m <= 1 / 2 ==> in_some m ivs
```

## S103  [INNER]

For: the matrix 2DP is n x n, symmetric, and y^T (2DP) y is twice the quadratic part of the state.

May use: S052, S038

```
st_wf n (ok,k,g,Cm,mL,mY,mM) /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> LENGTH (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) = n /\ EVERY (\r. LENGTH r = n) (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) /\ (!i j. i < n /\ j < n ==> EL j (EL i (inner_matrix ws (ok,k,g,Cm,mL,mY,mM))) = EL i (EL j (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)))) /\ qform (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) y y = (qform Cm y y + ldot mY y * ldot ws y + real_of_int mM * (ldot ws y * ldot ws y))
```

## S104  [SLAB]

For: the cut pairs enter exactly as theta*bound1 + (1-theta)*bound2, and every theta is in [0,1].

May use: S083, S138

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cut D n (1096 * 1096) zs st) ==> FST st /\ st_wf n (add_cut D n (1096 * 1096) zs st) /\ st_val ws (add_cut D n (1096 * 1096) zs st) y = st_val ws st y + &D * cut_val zs y /\ EVERY (\z. 0 <= FST (SND z) /\ FST (SND z) < &(SND (SND z))) zs
```

## S105  [INNER]

For: the rebuilt inner polynomial is D * (L0 - every multiplier term), and the multiplier terms are >= 0 on the region.

May use: S005, S130, S100, S048, S002, S059, S043, S139, S047

```
0 < D /\ LENGTH (y:real list) = n /\ FST (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) ==> st_wf n (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) /\ st_val ws (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) y = &D * (L0 ab cuts full y - mults_val (ldot ws y / 1096) (qv rp rq) lam nu (qv kp kq) nn cc y) /\ (in_box n y /\ 0 <= m /\ m <= rin ==> 0 <= mults_val m rin lam nu (qv kp kq) nn cc y)
```

## S106  [SLAB]

For: forms in m (kinds 7-13) subtract exactly mu * f(y), with m = (SUM W y)/1096, lo = lp/lq, hi = hp/hq.

May use: S135, S145

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ 7 <= kind /\ kind <= 13 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val (ldot ws y / 548) (qv lp lq) (qv hp hq) kind i j k s1 s2 s3 y
```

## S107  [SLAB]

For: the whole list of forms subtracts exactly SUM mu_f f(y).

May use: S008, S044, S148, S051

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_forms D n 1096 lp lq hp hq forms st) ==> FST st /\ st_wf n (add_forms D n 1096 lp lq hp hq forms st) /\ st_val ws (add_forms D n 1096 lp lq hp hq forms st) y = st_val ws st y - &D * forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y
```

## S108  [SLAB]

For: the integer test claim <= B - eps(1+n) means what it says in rationals.

May use: (nothing)

```
0 < Bq /\ 0 < eq /\ 0 < cq /\ (cp:int) * &(Bq:num) * &(eq:num) <= (Bp * &eq - ep * &(n + 1) * &Bq) * &(cq:num) ==> qv cp cq <= qv Bp Bq - qv ep eq * &(n + 1)
```

## S109  [INNER]

For: the matrix 2DP is n x n, symmetric, and y^T (2DP) y is twice the quadratic part of the state.

May use: S052, S038

```
st_wf n (ok,k,g,Cm,mL,mY,mM) /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> LENGTH (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) = n /\ EVERY (\r. LENGTH r = n) (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) /\ (!i j. i < n /\ j < n ==> EL j (EL i (inner_matrix ws (ok,k,g,Cm,mL,mY,mM))) = EL i (EL j (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)))) /\ qform (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) y y = 2 * (qform Cm y y + ldot mY y * ldot ws y + real_of_int mM * (ldot ws y * ldot ws y))
```

## S110  [SLAB]

For: add_term keeps the state well-formed, and an ok result means every guard held.

May use: S041, S021

```
(st_wf n st ==> st_wf n (add_term D n tag i j p q st)) /\ (FST (add_term D n tag i j p q st) ==> FST st /\ D MOD q = 0 /\ i < n /\ j < n /\ tag <= 5)
```

## S111  [INNER]

For: the rebuilt inner polynomial is D * (L0 - every multiplier term), and the multiplier terms are >= 0 on the region.

May use: S153, S085, S022, S147, S096, S020, S081, S162, S140

```
0 < D /\ LENGTH (y:real list) = n /\ FST (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) ==> st_wf n (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) /\ st_val ws (inner_poly D n ab cuts full rp rq lam nu kp kq nn cc) y = &D * (L0 ab cuts full y + mults_val (ldot ws y / 1096) (qv rp rq) lam nu (qv kp kq) nn cc y) /\ (in_box n y /\ 0 <= m /\ m <= rin ==> 0 <= mults_val m rin lam nu (qv kp kq) nn cc y)
```

## S112  [SLAB]

For: forms in m (kinds 7-13) subtract exactly mu * f(y), with m = (SUM W y)/1096, lo = lp/lq, hi = hp/hq.

May use: S135, S137

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ 7 <= kind /\ kind <= 13 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) kind i j k s1 s2 s3 y
```

## S113  [STRICT]

For: strict weighted dominance makes v^T M v > 0 for v <> 0 (strictness without leading minors).

May use: S040

```
dd_rows c1 c2 0 M Lw Lw ds ds /\ LENGTH Lw = LENGTH M /\ LENGTH ds = LENGTH M /\ EVERY (\r. LENGTH r = LENGTH M) M /\ (!i j. i < LENGTH M /\ j < LENGTH M ==> EL j (EL i M) = EL i (EL j M)) /\ 0 < c1 /\ 0 <= c2 ==> !v:real list. LENGTH v = LENGTH M ==> 0 <= qform M v v /\ (EXISTS (\x. x <> 0) v ==> 0 < qform M v v)
```

## S114  [COVER]

For: TOP (cover): the regions cover every m in [0, 1/2].

May use: S053

```
cover_all ivs ==> !m:real. 0 <= m /\ m <= 1 / 2 ==> in_some m ivs
```

## S115  [INNER]

For: m >= 0 on the box when the grid increases.

May use: S078

```
increasing grid /\ in_box (LENGTH grid - 1) y ==> 0 <= mval grid y
```

## S116  [SLAB]

For: the rebuilt slab polynomial is D * (L_theta - B - SUM mu_f f).

May use: S135, S137, S153, S033, S158, S071, S107

```
0 < D /\ LENGTH (y:real list) = n /\ FST (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) ==> st_wf n (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) /\ D MOD Bq = 0 /\ st_val ws (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) y = &D * (Ltheta ab cuts full theta y + qv Bp Bq - forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y)
```

## S117  [SLAB]

For: the helper of the triangle form subtracts c/q * z_a z_b, z = 1 - 2y.

May use: S110, S042

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_zz D n c q a b st) ==> FST st /\ st_wf n (add_zz D n c q a b st) /\ st_val ws (add_zz D n c q a b st) y = st_val ws st y - &D * qv c q * ((1 - 2 * EL a y) * (1 - 2 * EL b y))
```

## S118  [SLAB]

For: the accepted forms sum to something non-negative on the region.

May use: S157, S062, S141

```
FST (add_forms D n 1096 lp lq hp hq forms st) /\ LENGTH (y:real list) = n /\ lo <= m /\ m <= hi ==> 0 <= forms_val m lo hi forms y
```

## S119  [INNER]

For: the nu terms nu_j y_j (rin - m) are subtracted exactly and are >= 0 on the region.

May use: S135, S137

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nu D n 1096 rp rq j nu st) ==> FST st /\ st_wf n (add_nu D n 1096 rp rq j nu st) /\ st_val ws (add_nu D n 1096 rp rq j nu st) y = st_val ws st y - &D * nu_val (ldot ws y / 1096) (qv rp rq) j nu y /\ (in_box n y /\ m <= rin ==> 0 <= nu_val m rin j nu y)
```

## S120  [SLAB]

For: v^T M v at v = (1, y) is 2 * (the state polynomial) + 2 D eps |v|^2.

May use: S159, S038

```
st_wf n st /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> qform (slab_matrix D ep eq ws st) (1 :: y) (1 :: y) = 2 * st_val ws st y + 2 * real_of_int (sc D ep eq) * sumsq y
```

## S121  [INNER]

For: the matrix 2DP is n x n, symmetric, and y^T (2DP) y is twice the quadratic part of the state.

May use: S159, S038

```
st_wf n (ok,k,g,Cm,mL,mY,mM) /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> LENGTH (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) = n /\ EVERY (\r. LENGTH r = n) (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) /\ (!i j. i < n /\ j < n ==> EL j (EL i (inner_matrix ws (ok,k,g,Cm,mL,mY,mM))) = EL i (EL j (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)))) /\ qform (inner_matrix ws (ok,k,g,Cm,mL,mY,mM)) y y = 2 * (qform Cm y y + ldot mY y * ldot ws y + real_of_int mM * (ldot ws y * ldot ws y))
```

## S122  [SLAB]

For: adding v at (i, j) of a matrix adds v * u_i * y_j to its bilinear form, shape kept.

May use: S041

```
LENGTH (addm i j v Cm) = LENGTH Cm /\ (EVERY (\r. LENGTH r = n) Cm ==> EVERY (\r. LENGTH r = n) (addm i j v Cm)) /\ (i < LENGTH Cm /\ j < n /\ EVERY (\r. LENGTH r = n) Cm /\ LENGTH (u:real list) = LENGTH Cm /\ LENGTH (y:real list) = n ==> qform (addm i j v Cm) u y = qform Cm u y + real_of_int v * (EL j u * EL i y))
```

## S123  [SLAB]

For: |y|^2 <= n on the box.

May use: (nothing)

```
in_box n y ==> sumsq y <= &n
```

## S124  [SLAB]

For: v^T M v at v = (1, y) is 2 * (the state polynomial) + 2 D eps |v|^2.

May use: S052, S088

```
st_wf n st /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> qform (slab_matrix D ep eq ws st) (1 :: y) (1 :: y) = 2 * st_val ws st y + 2 * real_of_int (sc D ep eq) * sumsq y
```

## S125  [SLAB]

For: the matrix M = 2D(S + eps I) is (n+1) x (n+1) and symmetric.

May use: S052, S038

```
st_wf n st /\ LENGTH (ws:int list) = n ==> LENGTH (slab_matrix D ep eq ws st) = n /\ EVERY (\r. LENGTH r = n + 1) (slab_matrix D ep eq ws st) /\ !i j. i < n + 1 /\ j < n + 1 ==> EL j (EL i (slab_matrix D ep eq ws st)) = EL i (EL j (slab_matrix D ep eq ws st))
```

## S126  [SLAB]

For: TOP (slabs): if the check returns T then L_theta >= the claim everywhere on the region.

May use: S131, S068, S133, S016, S120, S025, S150, S034, S024

```
slab_check ab cuts full grid lp lq hp hq Bp Bq ep eq cp cq theta forms D T2 ds Lw ==> !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv hp hq ==> qv cp cq <= Ltheta ab cuts full theta y
```

## S127  [SLAB]

For: the rebuilt slab polynomial is D * (L_theta - B - SUM mu_f f).

May use: S161, S145, S153, S092, S158, S104, S091

```
0 < D /\ LENGTH (y:real list) = n /\ FST (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) ==> st_wf n (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) /\ D MOD Bq = 0 /\ st_val ws (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) y = &D * (Ltheta ab cuts full theta y - qv Bp Bq - forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y)
```

## S128  [INNER]

For: the nu terms nu_j y_j (rin - m) are subtracted exactly and are >= 0 on the region.

May use: S135, S137

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nu D n 1096 rp rq j nu st) ==> FST st /\ st_wf n (add_nu D n 1096 rp rq j nu st) /\ st_val ws (add_nu D n 1096 rp rq j nu st) y = st_val ws st y - &D * nu_val (ldot ws y / 1096) (qv rp rq) j nu y /\ (in_box n y ==> 0 <= nu_val m rin j nu y)
```

## S129  [INNER]

For: TOP (inner): if the check returns T then L0 >= 0 on the region, with equality only at y = 0.

May use: S150, S113, S111, S121, S065, S013

```
inner_check ab cuts full grid rp rq lam nu kp kq nn cc D T2 ds Lw ==> !y. in_box (LENGTH grid - 1) y /\ mval grid y <= qv rp rq ==> 0 < L0 ab cuts full y /\ (L0 ab cuts full y = 0 ==> EVERY (\x. x = 0) y)
```

## S130  [SLAB]

For: the per-cell terms a_i y_i + b_i y_i^2 enter exactly.

May use: S110, S042

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cells D n i ab st) ==> FST st /\ st_wf n (add_cells D n i ab st) /\ st_val ws (add_cells D n i ab st) y = st_val ws st y + &D * cells_val i ab y
```

## S131  [SLAB]

For: the integer p * (D DIV q) is exactly D * p/q when q divides D.

May use: (nothing)

```
0 < D ==> real_of_int (sc D p q) = &D * qv p q
```

## S132  [SLAB]

For: the rebuilt slab polynomial is D * (L_theta - B - SUM mu_f f).

May use: S083, S145, S153, S085, S080, S144, S097

```
0 < D /\ LENGTH (y:real list) = n /\ FST (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) ==> st_wf n (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) /\ D MOD Bq = 0 /\ st_val ws (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) y = &D * (Ltheta ab cuts full theta y - qv Bp Bq - forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y)
```

## S133  [SLAB]

For: the rebuilt slab polynomial is D * (L_theta - B - SUM mu_f f).

May use: S135, S138, S005, S094, S080, S012, S037

```
0 < D /\ LENGTH (y:real list) = n /\ FST (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) ==> st_wf n (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) /\ D MOD Bq = 0 /\ st_val ws (slab_poly D n ab cuts full Bp Bq lp lq hp hq theta forms) y = &D * (Ltheta ab cuts full theta y + qv Bp Bq - forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y)
```

## S134  [SLAB]

For: the matrix M = 2D(S + eps I) is (n+1) x (n+1) and symmetric.

May use: S159, S038

```
st_wf n st /\ LENGTH (ws:int list) = n ==> LENGTH (slab_matrix D ep eq ws st) = n + 1 /\ EVERY (\r. LENGTH r = n + 1) (slab_matrix D ep eq ws st) /\ !i j. i < n + 1 /\ j < n + 1 ==> EL j (EL i (slab_matrix D ep eq ws st)) = EL i (EL j (slab_matrix D ep eq ws st))
```

## S135  [SLAB]

For: add_term keeps the state well-formed, and an ok result means every guard held.

May use: S061, S122

```
(st_wf n st ==> st_wf n (add_term D n tag i j p q st)) /\ (FST (add_term D n tag i j p q st) ==> FST st /\ D MOD q = 0 /\ i < n /\ j < n /\ tag <= 5)
```

## S136  [SLAB]

For: v^T M v at v = (1, y) is 2 * (the state polynomial) + 2 D eps |v|^2.

May use: S052, S038

```
st_wf n st /\ LENGTH (ws:int list) = n /\ LENGTH (y:real list) = n ==> qform (slab_matrix D ep eq ws st) (1 :: y) (1 :: y) = 2 * st_val ws st y + 2 * real_of_int (sc D ep eq) * sumsq y
```

## S137  [SLAB]

For: one accepted term adds exactly D * (p/q) * its monomial.

May use: S017, S041, S021, S135

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n ==> st_val ws (add_term D n tag i j p q st) y = st_val ws st y + &D * qv p q * mono ws tag i j y
```

## S138  [SLAB]

For: one accepted term adds exactly D * (p/q) * its monomial.

May use: S131, S061, S122, S083

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n ==> st_val ws (add_term D n tag i j p q st) y = st_val ws st y + &D * qv p q * mono ws tag i j y
```

## S139  [INNER]

For: y^T N y (upper triangle given) is subtracted exactly and is >= 0 on the box.

May use: S110, S042

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nn D n nn st) ==> FST st /\ st_wf n (add_nn D n nn st) /\ st_val ws (add_nn D n nn st) y = st_val ws st y - &D * nn_val nn y /\ (in_box n y ==> 0 <= nn_val nn y)
```

## S140  [INNER]

For: the linear terms c_i y_i are subtracted exactly and are >= 0 on the box.

May use: S161, S145

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cc D n i cc st) ==> FST st /\ st_wf n (add_cc D n i cc st) /\ st_val ws (add_cc D n i cc st) y = st_val ws st y - &D * cc_val (i + 1) cc y /\ (in_box n y ==> 0 <= cc_val i cc y)
```

## S141  [SLAB]

For: the triangle inequality 1 + s1 ab + s2 bc + s3 ac >= 0 on the cube when s1 s2 s3 = 1.

May use: (nothing)

```
-1 <= a /\ a <= 1 /\ -1 <= b /\ b <= 1 /\ -1 <= c /\ c <= (1:real) /\ ((s1:int) = 1 \/ s1 = -1) /\ (s2 = 1 \/ s2 = -1) /\ (s3 = 1 \/ s3 = -1) ==> 0 <= 1 + real_of_int s1 * (a * b) + real_of_int s2 * (b * c) + real_of_int s3 * (a * c)
```

## S142  [INNER]

For: the cut pairs of L0 (the bound that vanishes at 0) enter exactly.

May use: S161, S137

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cut0 D n (1096 * 1096) cuts st) ==> FST st /\ st_wf n (add_cut0 D n (1096 * 1096) cuts st) /\ st_val ws (add_cut0 D n (1096 * 1096) cuts st) y = st_val ws st y + &D * cut0_val cuts y
```

## S143  [INNER]

For: the linear part after expanding m, and: an all-zero list has dot product 0.

May use: S088

```
(LENGTH (ws:int list) = LENGTH g /\ LENGTH (y:real list) = LENGTH g ==> ldot (lin mL ws g) y = ldot g y - real_of_int mL * ldot ws y) /\ (all_zero l ==> ldot l y = 0)
```

## S144  [SLAB]

For: the cut pairs enter exactly as theta*bound1 + (1-theta)*bound2, and every theta is in [0,1].

May use: S135, S138

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cut D n (1096 * 1096) zs st) ==> FST st /\ st_wf n (add_cut D n (1096 * 1096) zs st) /\ st_val ws (add_cut D n (1096 * 1096) zs st) y = st_val ws st y + &D * cut_val zs y /\ EVERY (\z. 0 <= FST (SND z) /\ FST (SND z) < &(SND (SND z))) zs
```

## S145  [SLAB]

For: one accepted term adds exactly D * (p/q) * its monomial.

May use: S131, S061, S067, S135

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n ==> st_val ws (add_term D n tag i j p q st) y = st_val ws st y + &D * qv p q * mono ws tag i j y
```

## S146  [SLAB]

For: the whole list of forms subtracts exactly SUM mu_f f(y).

May use: S095, S084, S098, S089

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_forms D n 1096 lp lq hp hq forms st) ==> FST st /\ st_wf n (add_forms D n 1096 lp lq hp hq forms st) /\ st_val ws (add_forms D n 1096 lp lq hp hq forms st) y = st_val ws st y - &D * forms_val (ldot ws y / 1096) (qv lp lq) (qv hp hq) forms y
```

## S147  [INNER]

For: the cut pairs of L0 (the bound that vanishes at 0) enter exactly.

May use: S083, S138

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_cut0 D n (1096 * 1096) cuts st) ==> FST st /\ st_wf n (add_cut0 D n (1096 * 1096) cuts st) /\ st_val ws (add_cut0 D n (1096 * 1096) cuts st) y = st_val ws st y - &D * cut0_val cuts y
```

## S148  [SLAB]

For: forms in m (kinds 7-13) subtract exactly mu * f(y), with m = (SUM W y)/1096, lo = lp/lq, hi = hp/hq.

May use: S161, S137

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ 7 <= kind /\ kind <= 13 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val (ldot ws y / 548) (qv lp lq) (qv hp hq) kind i j k s1 s2 s3 y
```

## S149  [SLAB]

For: TOP (slabs): if the check returns T then L_theta >= the claim everywhere on the region.

May use: S017, S154, S019, S027, S057, S123, S078, S040, S108

```
slab_check ab cuts full grid lp lq hp hq Bp Bq ep eq cp cq theta forms D T2 ds Lw ==> !y. in_box (LENGTH grid - 1) y /\ qv lp lq <= mval grid y /\ mval grid y <= qv hp hq ==> qv cp cq <= Ltheta ab cuts full theta y
```

## S150  [SLAB]

For: a grid of n+1 points has n widths.

May use: (nothing)

```
LENGTH (widths grid) = LENGTH grid
```

## S151  [SLAB]

For: forms in the y's alone (kinds 0-6) subtract exactly mu * f(y).

May use: S083, S145

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ kind <= 6 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i j k s1 s2 s3 y
```

## S152  [SLAB]

For: every non-triangle form is non-negative on the region.

May use: (nothing)

```
in_box n y /\ lo <= m /\ m <= hi /\ kind <= 13 /\ form_idx_ok n kind i j k ==> 0 <= form_val m lo hi kind i j k s1 s2 s3 y
```

## S153  [SLAB]

For: the empty state is well-formed, ok, and stands for the zero polynomial.

May use: (nothing)

```
st_wf n (st0 n) /\ FST (st0 n) /\ (LENGTH (y:real list) = n ==> st_val ws (st0 n) y = 1)
```

## S154  [SLAB]

For: the accepted forms sum to something non-negative on the region.

May use: S095, S152, S054

```
FST (add_forms D n 1096 lp lq hp hq forms st) /\ in_box n y /\ lo <= m /\ m <= hi ==> 0 <= forms_val m lo hi forms y
```

## S155  [SLAB]

For: the helper of the triangle form subtracts c/q * z_a z_b, z = 1 - 2y.

May use: S135, S137

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_zz D n c q a b st) ==> FST st /\ st_wf n (add_zz D n c q a b st) /\ st_val ws (add_zz D n c q a b st) y = st_val ws st y - &D * qv c q * ((1 - 2 * EL a y) * (1 - 2 * EL b y))
```

## S156  [SLAB]

For: forms in the y's alone (kinds 0-6) subtract exactly mu * f(y).

May use: S135, S137

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ kind <= 7 /\ FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> st_wf n (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) /\ st_val ws (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) y = st_val ws st y - &D * qv mp mq * form_val m lo hi kind i j k s1 s2 s3 y
```

## S157  [SLAB]

For: an accepted form has a non-negative multiplier, a known kind, indices in range, and a legal triangle sign pattern.

May use: S083

```
FST (add_form D n 1096 lp lq hp hq kind i j k s1 s2 s3 mp mq st) ==> FST st /\ 0 < mp /\ kind <= 14 /\ form_idx_ok n kind i j k /\ (kind = 14 ==> (s1 = 1 \/ s1 = -1) /\ (s2 = 1 \/ s2 = -1) /\ (s3 = 1 \/ s3 = -1) /\ s1 * s2 * s3 = 1)
```

## S158  [SLAB]

For: the full pairs enter exactly.

May use: S135, S145

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_full D n 1096 full st) ==> FST st /\ st_wf n (add_full D n 1096 full st) /\ st_val ws (add_full D n 1096 full st) y = st_val ws st y + &D * full_val full y
```

## S159  [SLAB]

For: transp is the transpose.

May use: (nothing)

```
EVERY (\r. LENGTH r = n) (Cm:int list list) ==> LENGTH (transp n Cm) = n /\ EVERY (\r. LENGTH r = LENGTH Cm) (transp n Cm) /\ !i j. i < n /\ j < LENGTH Cm ==> EL j (EL i (transp n Cm)) = EL j (EL i Cm)
```

## S160  [STRICT]

For: strict weighted dominance makes v^T M v > 0 for v <> 0 (strictness without leading minors).

May use: S034

```
sdd_rows c1 c2 0 M Lw Lw ds ds /\ LENGTH Lw = LENGTH M /\ LENGTH ds = LENGTH M /\ EVERY (\r. LENGTH r = LENGTH M) M /\ (!i j. i < LENGTH M /\ j < LENGTH M ==> EL j (EL i M) = EL i (EL j M)) /\ 0 < c1 /\ 0 <= c2 ==> !v:real list. LENGTH v = LENGTH M ==> 0 <= qform M v v /\ (EXISTS (\x. x <> 0) v ==> 0 < qform M v v)
```

## S161  [SLAB]

For: add_term keeps the state well-formed, and an ok result means every guard held.

May use: S061, S067

```
(st_wf n st ==> st_wf n (add_term D n tag i j p q st)) /\ (FST (add_term D n tag i j p q st) ==> FST st /\ D MOD q = 0 /\ i < n /\ j < n /\ tag <= 5)
```

## S162  [INNER]

For: y^T N y (upper triangle given) is subtracted exactly and is >= 0 on the box.

May use: S135, S145

```
0 < D /\ st_wf n st /\ LENGTH (y:real list) = n /\ FST (add_nn D n nn st) ==> FST st /\ st_wf n (add_nn D n nn st) /\ st_val ws (add_nn D n nn st) y = st_val ws st y - &D * (2 * nn_val nn y) /\ (in_box n y ==> 0 <= nn_val nn y)
```
