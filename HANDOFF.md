# Handoff: Lean fixes (cluster session)

Build Lean only on the cluster (`lake build` in `formalization/`). The thesis is in `tex/`. Each `\LeanResult{label}` link is defined in `tex/preamble/lean_links_generated.tex`; the links for commit 00d50081 are in `lean_links_draft.tex`. Table A.2 is `tex/tables/lean_coverage.tex` (marker c = component only). All links are pinned to 86afca49 or 00d50081.

## Conventions for every Lean change
- One definition per concept, used throughout wherever possible: one MLP (weights, biases, per-layer activations), one activation-function type, one split/decomposition pair, one trajectory law. Remove parallel encodings or connect them by a lemma. Known duplicates: `Games.pathLaw` vs `TrajectoryHellinger.pathLaw`; `Network.split` vs `Network.affineHeads`; `Network.common` vs `absCLM`/`absoluteMap`; the single-activation `forwardWith`.
- Use Mathlib wherever possible instead of hand-rolled notions, e.g. `ConvexOn`, `Monotone`/`MonotoneOn`, `HasDerivAt`/`HasFDerivAt`, `Filter.Tendsto` for limits, `Finset` sums, `Real.sqrt`/`Real.log`, measure theory for a.e. statements.

## Thesis changes already made (2026-11-25); Lean must match
- Theorem 3.16 (`thm:shift_forward`): no non-negativity hypothesis.
- Theorem 3.17 (`thm:closed_formula_shift`): holds for any complementary 0/1 selection M^(l,+) + M^(l,-) = I. Here δ^(l) is the product of the M^(l,+)-gated matrices. Lean gates with 0 < z; the thesis Maxout convention with z ≥ 0.

## 1. Lean changes
1. Lean_65 `Thesis.AttentionBackward.thesis_attention_alpha_beta_recovery` (Thesis/AttentionBackward.lean:177): weaken `0 < ε` to `0 ≤ ε`. The hypothesis is unused, and the thesis shows the ε = 0 formulas.
2. Lean_37 and (3.43): `Network.shift` covers the gated layers only. Add the readout step as a corollary for `Network.affineHeads`: both heads shift by `(rp+rn) (net.common c)`. Also prove `Network.common = absoluteMap`.
3. Lean_39: give a pointwise version on strict cells for any complementary mask, building on `MaskedTrace.pull_unified`, `run_bulk`, `run_unified` and `affine_readout_closed_form` (AffineReadout.lean:60). The current link is only almost-everywhere at l = 0.
4. Lean_17 `SmoothDC.normalized_curvature_monotone_dc_split` (CurvatureMonotoneDCLift.lean:205): add the s_+ limit and `curvatureLiftWidth = (‖f''‖₁+|s_-|+|s_+|)/2`. Add the identity p, q = (D±f)/2.
5. (2.36): add a bridge lemma from `pathDisagreement` (Games.lean:244) to the form with the recursively computed overlap g^(0)(s).
6. Optional: per-layer activations in `forwardWith` (Lean_5, Lean_6); Routing Game contraction as a pushforward (Lean_66); the anchor law of `rgOccupation` equals the SPNE of Theorem 4.5 (behind (4.29)).
7. Build roots: import `Thesis.TrajectoryHellinger`, `Thesis.PolarizedMultiplicative` and `HiddenMonotonicity.TransformerLinearCost` in `All.lean`. At present only `checks/*.lean` import them.
8. README: drop "unpublished" and the draft-proofs links for TrajectoryHellinger (l.259–263), and add the build command for PolarizedMultiplicative.

## 2. Links (after the build passes; re-pin all links to the new commit)
- Write the missing generator for `lean_links_generated.tex` and `lean_coverage.tex`; the appendix calls Table A.2 generated.
- Re-link: Lean_57 → `SignedExpr.split_correct` / `split_streams_monotone` (MultiplicativeSplit.lean:51/:103); Lean_12 and (2.34) → `TrajectoryHellinger.BC_eq_path_overlap` (:156); Lean_39 → item 1.3; Lean_44 → `relu_net_game_value` (SourceFoundationsStatements.lean:228); (3.42) → `Network.absCLM_eq_absoluteMap` (OriginalTrace.lean:172); (3.6) → definition `asymmetricLift`; (4.25): add `layerGames_selected_gate` (L303); (4.36) → `softplus_variational` (L138); (5.4) → its definition; Lean_66 → `hellinger_coarsening` (Coarsening.lean:74).
- Marker c (drop it where item 1 closes the gap): Ch2 5, 6, 10, 11, 13, 14; Ch3 16, 17, 20, 22, 25, 29, 30, 35, 36, 37, 39; Ch4 45, 46, 49, 51, 54; Ch5 56, 62, 63, 64; Ch7 66.
- Fix the Table A.2 rows: Lean_11, Lean_12 → Theorem 2.10; Lean_19 → Theorem 3.6; Lean_32 → Lemma 3.12 (same declaration as Lean_31; merge them); Lean_41 → Lemma 3.18.
- Delete the dead mapping entries `ptnb:eq:conditioned-bc-kernel`, `eq:delta_int_neg`, `eq:closed_formula_h`, and the stale ones (`prop:multivariate_dc_lift`, Lean_68, Lean_69, and the others no label uses).

## 3. Finish
Rebuild the thesis with 0 undefined references and copy `tex/main.pdf` to `formalization/thesis.pdf`. Commit only when asked.
