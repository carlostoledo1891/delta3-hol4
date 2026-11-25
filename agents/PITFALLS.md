# HOL4 pitfalls met while building this harness (the same note for both model families)

Seven things that cost judged attempts, found at HOL4 trindemossen-2-v9 while proving one of the lemmas.
They are about the prover, not about any statement: nothing here says which statements are true.

1. **`simp`, `rw` and `fs` rewrite with the assumptions; an induction hypothesis whose right side contains its
   left side loops.**
   Example: after `Induct`, the hypothesis `!acc ys. dot acc xs ys = acc + dot 0 xs ys` makes `simp[]` rewrite
   `dot 0 xs ys` to `0 + dot 0 xs ys` and back, forever. Instantiate it instead:
   `first_assum (qspecl_then [`acc + h * h'`, `t`] SUBST1_TAC)`.

2. **`REAL_ARITH_TAC` eliminates `abs` (and conditionals) everywhere, also inside a lambda, and then does not
   finish.** A goal like `S <= 2 * h ==> 0 <= 2 * h - S` with `S = sum (count n) (\j. abs (H i j))` hangs.
   Generalise each sum to a variable first: `qspec_tac (`sum (count n) (\j. abs (H i j))`, `s`) >> REAL_ARITH_TAC`.

3. **`rewrite_tac` matches first-order; a lemma about `\x. f x - g x` does not fire on a concrete lambda, and
   `irule` with such a lemma can return the η-short `f i` where the goal has `\j. f i j`.**
   Example: `irule SUM_SUB'` fails on `sum s (\j. f i j - g i j) = sum s (\j. f i j) - sum s (\j. g i j)`;
   `simp_tac (srw_ss()) [SUM_SUB', FINITE_COUNT]` proves it, or instantiate the lemma explicitly with
   `qspecl_then [`\j. ...`, `\j. ...`, `s`] (mp_tac o BETA_RULE) SUM_SUB'`.

4. **A variable with the name of a constant does not parse as that variable inside tactic quotations.**
   Example: with `!n K x p. ...` in the goal, a `by` quotation mentioning `count K` reads `K` as the K combinator
   (`K : 'a -> 'b -> 'a`) and fails to type-check. Use another name (`nk`).

5. **Rewriting with a symmetry theorem loops.**
   Example: `rewrite_tac [EQ_SYM_EQ]` to turn `~(a = x)` into `~(x = a)` never stops; prove the flipped fact by
   `strip_tac >> qpat_x_assum `~(a = x)` mp_tac >> asm_rewrite_tac []`.

6. **Some library theorems are stored with FREE variables, not universally quantified, and `qspecl_then` /
   `Q.SPECL` cannot instantiate them.**
   Example: `intrealTheory.real_of_int_le` is `real_of_int m <= real_of_int n <=> m <= n` (m, n free);
   `qspecl_then [`x`, `0`] mp_tac real_of_int_le` fails. Restate it as a quantified local lemma
   (`!m n. ... ` proved by `rewrite_tac [real_of_int_le]`), or use it only as a rewrite.

7. **`real_sigma`'s finite `sum` over a set is the constant `Sum` (printed `sum`); `realTheory`'s `sum (m,n)` is
   another constant.** Code that looks for the constant by name must use `"Sum"`; and `sum (count n) f` with
   `real_sigma` in the ancestry is the set form, for which `SUM_SWAP_COUNT`, `SUM_DELTA`, `SUM_LMUL`, `SUM_RMUL`,
   `SUM_DELETE`, `SUM_POS_LE`, `SUM_POS_LT` exist.

Also useful: a definition whose right-hand side is a `case` (such as `rowsum_def`, `dd_rows_def`) is ONE recursive
equation; unfold it with `once_rewrite_tac [rowsum_def]`, never `simp [rowsum_def]` (it unfolds forever), and reduce
the resulting `case` with `simp_tac bool_ss [list_case_def]` (it also beta-reduces).
