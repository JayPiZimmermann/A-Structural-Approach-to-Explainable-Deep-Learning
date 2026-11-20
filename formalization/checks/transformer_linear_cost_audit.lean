import HiddenMonotonicity.TransformerLinearCost

noncomputable section
open HiddenMonotonicity.TransformerDC Set

/-- Independent spelling of the complete source-facing contract. -/
example {t d o : ℕ} (net : Transformer t d o) :
    (∀ x i, (net.sharedDecompose x).val.get i = net.decompose x i) ∧
    (∀ x, (net.sharedDecompose x).steps ≤ 200 * SharedRuntime.networkSize net) ∧
    MonotoneOn net.decompose (Ici (0 : DoubledInput (Fin t × Fin d))) ∧
    (∀ i, ConvexOn ℝ (Ici (0 : DoubledInput (Fin t × Fin d)))
      (fun x => (net.decompose x i).1)) ∧
    (∀ i, ConvexOn ℝ (Ici (0 : DoubledInput (Fin t × Fin d)))
      (fun x => (net.decompose x i).2)) ∧
    (∀ x, 0 ≤ x → 0 ≤ net.decompose x) ∧
    (∀ x i, (net.decompose x i).1 - (net.decompose x i).2 =
      net.eval (x.1 - x.2) i) ∧
    (∀ i, ConvexOn ℝ univ
      (fun x : Fin t × Fin d → ℝ => (net.rawDecompose x i).1)) ∧
    (∀ i, ConvexOn ℝ univ
      (fun x : Fin t × Fin d → ℝ => (net.rawDecompose x i).2)) ∧
    (∀ x, 0 ≤ net.rawDecompose x) ∧
    (∀ x i, (net.rawDecompose x i).1 - (net.rawDecompose x i).2 = net.eval x i) :=
  net.dc_decomposition_linear_cost

/-- The counted execution itself recovers the output. -/
example {t d o : ℕ} (net : Transformer t d o)
    (x : DoubledInput (Fin t × Fin d)) (i : Fin o) :
    ((net.sharedDecompose x).val.get i).1 - ((net.sharedDecompose x).val.get i).2 =
      net.eval (x.1 - x.2) i := by
  rw [net.sharedDecompose_eq x i]
  exact net.decompose_exact x i

#print HiddenMonotonicity.TransformerDC.Transformer.dc_decomposition_linear_cost
#print axioms HiddenMonotonicity.TransformerDC.Transformer.dc_decomposition_linear_cost
#print axioms HiddenMonotonicity.TransformerDC.Transformer.sharedDecompose_eq

end
