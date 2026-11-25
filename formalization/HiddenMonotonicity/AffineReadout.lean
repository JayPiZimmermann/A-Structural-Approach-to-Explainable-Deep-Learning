import HiddenMonotonicity.QSources

namespace HiddenMonotonicity
namespace MaskedTrace

/-- The same implemented shifted backward pass with arbitrary terminal head
partials. This includes an ungated, signed final affine readout. -/
noncomputable def run {n m} : MaskedTrace n m → (ℕ → ℝ) → Sensitivity m → Sensitivity n
  | .output _, α, seed => shiftPair (α 0) seed
  | .layer wp wn gate tail, α, seed =>
      shiftPair (α 0) (pull wp wn gate (tail.run (fun i => α (i+1)) seed))

theorem run_bulk {n m} (tr : MaskedTrace n m) (α : ℕ → ℝ) (seed : Sensitivity m) :
    (tr.run α seed).1+(tr.run α seed).2 =
      tr.bulkCoefficient α • ((seed.1+seed.2).comp tr.absMap) := by
  induction tr generalizing α with
  | output n => simp only [run, shiftPair_sum, bulkCoefficient, absMap, ContinuousLinearMap.comp_id]
  | layer wp wn gate tail ih =>
      simp only [run, shiftPair_sum, pull_sum, ih, bulkCoefficient, absMap,
        ContinuousLinearMap.smul_comp, smul_smul, ContinuousLinearMap.comp_assoc]

theorem run_unified {n m} (tr : MaskedTrace n m) (α : ℕ → ℝ) (seed : Sensitivity m) :
    unified (tr.run α seed) = (unified seed).comp tr.originalJac -
      (1/2 : ℝ) • tr.correction α (seed.1+seed.2) := by
  induction tr generalizing α with
  | output n => simp [run, unified_shift, originalJac, correction]
  | layer wp wn gate tail ih =>
      simp only [run, unified_shift, pull_unified, ih, run_bulk, originalJac, correction]
      apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
      ring

/-- An arbitrary terminal seed is the actual Fréchet differential when α=0. -/
theorem run_zero_actual {n m} (tr : MaskedTrace n m) (seed : Sensitivity m) :
    assemble (tr.run (fun _ => 0) seed) = (assemble seed).comp tr.splitJac := by
  induction tr with
  | output n => simp [run, shiftPair, splitJac]
  | layer wp wn gate tail ih =>
      simp only [run, shiftPair, zero_smul, sub_zero, pull, ih, splitJac,
        ContinuousLinearMap.comp_assoc]
      exact assemble_partialPair _

theorem run_stabilized {n m} (tr : MaskedTrace n m) (α : ℕ → ℝ) (r : Row m) (head : Bool) :
    tr.run α (if head then (r,0) else (0,r)) = tr.stabilized α r head := by
  induction tr generalizing α with
  | output n => rfl
  | layer wp wn gate tail ih => simp only [run, stabilized, ih]

end MaskedTrace

/-- The final affine readout splits as rPlus-rMinus with a fixed bias.
β is the shift at the scalar output; α ranges over the preceding activation layers. -/
noncomputable def affineReadoutSeed {m} (rPlus rMinus : Row m) (β : ℝ) (head : Bool) : Sensitivity m :=
  shiftPair β (if head then (rPlus,rMinus) else (rMinus,rPlus))

/-- Complete stabilized backward formulas for a ReLU backbone followed by an
ungated signed affine logit readout. All layer widths and biases are allowed. -/
theorem Network.affine_readout_closed_form {n m} (net : Network n m)
    (hc : net.Canonical) (x : Vec n) (hx : net.Strict x) (α : ℕ → ℝ)
    (rPlus rMinus : Row m) (β : ℝ) :
    (∀ q ∈ net.absoluteQSources x α, HasFDerivAt q.value q.jacobian x) ∧
    unified ((net.originalTrace x).run α (affineReadoutSeed rPlus rMinus β true)) =
      (1/2 : ℝ) • ((rPlus-rMinus).comp (net.originalTrace x).originalJac -
        (sourceRows (net.absoluteQSources x α) ((1-2*β) • (rPlus+rMinus))).sum) ∧
    unified ((net.originalTrace x).run α (affineReadoutSeed rPlus rMinus β false)) =
      (-1/2 : ℝ) • ((rPlus-rMinus).comp (net.originalTrace x).originalJac +
        (sourceRows (net.absoluteQSources x α) ((1-2*β) • (rPlus+rMinus))).sum) := by
  have hq := (net.stabilized_backward_absolute_Q_closed_form hc x hx α rPlus).1
  refine ⟨hq, ?_, ?_⟩
  · rw [MaskedTrace.run_unified]
    simp only [affineReadoutSeed, ite_true]
    rw [unified_shift, shiftPair_sum]
    simp only [unified]
    rw [← net.qSources_eq_absolute hc, net.qSources_sum]
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul]
    ring
  · rw [MaskedTrace.run_unified]
    simp only [affineReadoutSeed, Bool.false_eq_true, ite_false]
    rw [unified_shift, shiftPair_sum]
    simp only [unified]
    rw [add_comm rMinus rPlus]
    rw [← net.qSources_eq_absolute hc, net.qSources_sum]
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
    ring

/-- The ordinary gradient of the target affine logit, including arbitrary
readout bias, with the same original masked Jacobian used in the closed formula. -/
theorem Network.affine_logit_derivative {n m} (net : Network n m)
    (x : Vec n) (hx : net.Strict x) (rPlus rMinus : Row m) (bias : ℝ) :
    HasFDerivAt (fun y => (rPlus-rMinus) (net.eval y)+bias)
      ((rPlus-rMinus).comp (net.originalTrace x).originalJac) x :=
  ((rPlus-rMinus).hasFDerivAt.comp x (net.hasFDerivAt_originalTrace x hx)).add_const bias

/-- Pointwise closed formulas of the shifted backward pass for an arbitrary
fixed 0/1 gate selection. The inactive selection is the complement of the
active one by construction of `MaskedTrace`, so this covers every complementary
mask, including either convention at ties. The correction is the explicit
finite list of layer terms; the affine readout contributes none. -/
theorem MaskedTrace.affine_readout_closed_form {n m} (tr : MaskedTrace n m)
    (α : ℕ → ℝ) (rPlus rMinus : Row m) (β : ℝ) :
    unified (tr.run α (affineReadoutSeed rPlus rMinus β true)) =
      (1/2 : ℝ) • ((rPlus-rMinus).comp tr.originalJac -
        (tr.correctionTerms α ((1-2*β) • (rPlus+rMinus))).sum) ∧
    unified (tr.run α (affineReadoutSeed rPlus rMinus β false)) =
      (-1/2 : ℝ) • ((rPlus-rMinus).comp tr.originalJac +
        (tr.correctionTerms α ((1-2*β) • (rPlus+rMinus))).sum) := by
  rw [tr.correction_terms_sum]
  constructor
  · rw [MaskedTrace.run_unified]
    simp only [affineReadoutSeed, ite_true]
    rw [unified_shift, shiftPair_sum]
    simp only [unified]
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul]
    ring
  · rw [MaskedTrace.run_unified]
    simp only [affineReadoutSeed, Bool.false_eq_true, ite_false]
    rw [unified_shift, shiftPair_sum]
    simp only [unified]
    rw [add_comm rMinus rPlus]
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
    ring

/-- The bulk of the shifted pair for an arbitrary gate selection: the product
of the shift factors times the common-mode map. -/
theorem MaskedTrace.affine_readout_bulk {n m} (tr : MaskedTrace n m)
    (α : ℕ → ℝ) (rPlus rMinus : Row m) (β : ℝ) (head : Bool) :
    (tr.run α (affineReadoutSeed rPlus rMinus β head)).1 +
      (tr.run α (affineReadoutSeed rPlus rMinus β head)).2 =
      (tr.bulkCoefficient α * (1-2*β)) • ((rPlus+rMinus).comp tr.absMap) := by
  rw [tr.run_bulk]
  cases head <;>
    simp only [affineReadoutSeed, Bool.false_eq_true, ite_false, ite_true, shiftPair_sum,
      ContinuousLinearMap.smul_comp, smul_smul, add_comm rMinus rPlus]

/-- The backward invariant for an arbitrary gate selection and arbitrary shifts. -/
theorem MaskedTrace.affine_readout_invariant {n m} (tr : MaskedTrace n m)
    (α : ℕ → ℝ) (rPlus rMinus : Row m) (β : ℝ) :
    unified (tr.run α (affineReadoutSeed rPlus rMinus β true)) -
      unified (tr.run α (affineReadoutSeed rPlus rMinus β false)) =
      (rPlus-rMinus).comp tr.originalJac := by
  rw [(tr.affine_readout_closed_form α rPlus rMinus β).1,
    (tr.affine_readout_closed_form α rPlus rMinus β).2]
  module

/-- Thesis thm:closed_formula_shift, pointwise on strict activation cells. The
gate selection is the one of the forward pass, the masked product is the actual
derivative of the affine logit, and both shifted formulas hold with the explicit
finite sum of layer corrections. No sign condition on the weight parts is used. -/
theorem Network.affine_closed_form_strict {n m} (net : Network n m)
    (x : Vec n) (hx : net.Strict x) (α : ℕ → ℝ)
    (rPlus rMinus : Row m) (bp bn β : ℝ) :
    HasFDerivAt (fun y => (rPlus-rMinus) (net.eval y)+(bp-bn))
      ((rPlus-rMinus).comp (net.originalTrace x).originalJac) x ∧
    unified ((net.originalTrace x).run α (affineReadoutSeed rPlus rMinus β true)) =
      (1/2 : ℝ) • ((rPlus-rMinus).comp (net.originalTrace x).originalJac -
        ((net.originalTrace x).correctionTerms α ((1-2*β) • (rPlus+rMinus))).sum) ∧
    unified ((net.originalTrace x).run α (affineReadoutSeed rPlus rMinus β false)) =
      (-1/2 : ℝ) • ((rPlus-rMinus).comp (net.originalTrace x).originalJac +
        ((net.originalTrace x).correctionTerms α ((1-2*β) • (rPlus+rMinus))).sum) ∧
    unified ((net.originalTrace x).run α (affineReadoutSeed rPlus rMinus β true)) -
      unified ((net.originalTrace x).run α (affineReadoutSeed rPlus rMinus β false)) =
      (rPlus-rMinus).comp (net.originalTrace x).originalJac :=
  ⟨net.affine_logit_derivative x hx rPlus rMinus (bp-bn),
    ((net.originalTrace x).affine_readout_closed_form α rPlus rMinus β).1,
    ((net.originalTrace x).affine_readout_closed_form α rPlus rMinus β).2,
    (net.originalTrace x).affine_readout_invariant α rPlus rMinus β⟩

end HiddenMonotonicity
