import HiddenMonotonicity.TransformerCostCore

/-! Scalar-operation schedules for the actual closed-form activation pairs.
Constants fixed by the activation parameters are available as scalar constants;
all input-dependent arithmetic and special-function calls are charged explicitly.
The Gaussian CDF is one real-arithmetic primitive, as in the original GELU. -/
noncomputable section
set_option autoImplicit false

namespace HiddenMonotonicity.TransformerDC.SharedCost
open HiddenMonotonicity.SmoothDC

def sigmoidEval (z : ℝ) : Costed ℝ := do
  let nz ← neg z
  let e ← exp nz
  let s ← add 1 e
  inv s

def softplusEval (θ z : ℝ) : Costed ℝ := do
  let u ← div z θ
  let e ← exp u
  let s ← add 1 e
  let l ← log s
  mul θ l

def gaussianDensityEval (z : ℝ) : Costed ℝ := do
  let zz ← mul z z
  let nzz ← neg zz
  let u ← div nzz 2
  let e ← exp u
  mul (Real.sqrt (2 * Real.pi))⁻¹ e

/-- Evaluate each common scalar quantity once and reuse it in both heads. -/
def activation (φ : ClosedFormActivation) (x : ℝ × ℝ) : Costed (ℝ × ℝ) :=
  match φ with
  | .relu => do
      let p ← max x.1 x.2
      pure (p, x.2)
  | .gaussianGelu => do
      let d ← sub x.1 x.2
      let c ← cdf d
      let g ← mul d c
      let density ← gaussianDensityEval d
      let twiceDensity ← mul 2 density
      let pbase ← add g density
      let p ← mul 2 pbase
      let q ← add g twiceDensity
      let shift ← mul 2 x.2
      let p' ← add p shift
      let q' ← add q shift
      pure (p', q')
  | .swish β _ => do
      let d ← sub x.1 x.2
      let θ ← div 1 β
      let sp ← softplusEval θ d
      let p ← mul 2 sp
      let u ← mul β d
      let gate ← sigmoidEval u
      let f ← mul d gate
      let q ← sub p f
      let shift ← mul 2 x.2
      let p' ← add p shift
      let q' ← add q shift
      pure (p', q')
  | .sigmoid => do
      let d ← sub x.1 x.2
      let sp ← softplusEval 1 d
      let sig ← sigmoidEval d
      let pnum ← add sp sig
      let qnum ← sub sp sig
      let p ← div pnum 2
      let q ← div qnum 2
      let shift ← mul (1 / 2) x.2
      let p' ← add p shift
      let q' ← add q shift
      pure (p', q')
  | .softplus θ _ => do
      let d ← sub x.1 x.2
      let sp ← softplusEval θ d
      let p ← add sp x.2
      pure (p, x.2)

@[simp] theorem sigmoidEval_val (z : ℝ) :
    (sigmoidEval z).val = Real.sigmoid z := by
  rfl

@[simp] theorem softplusEval_val (θ z : ℝ) :
    (softplusEval θ z).val = Thesis.Regularization.softplus θ z := by
  rfl

@[simp] theorem gaussianDensityEval_val (z : ℝ) :
    (gaussianDensityEval z).val = standardGaussianDensity z := by
  rw [standardGaussianDensity_formula]
  change (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(z * z) / 2) = _
  rw [pow_two]

@[simp] theorem activation_val (φ : ClosedFormActivation) (x : ℝ × ℝ) :
    (activation φ x).val = φ.pair x := by
  cases φ with
  | relu =>
      rw [ClosedFormActivation.relu_pair]
      rfl
  | gaussianGelu =>
      change
        (2 * (gaussianGelu (x.1 - x.2) + (gaussianDensityEval (x.1 - x.2)).val) + 2 * x.2,
         gaussianGelu (x.1 - x.2) + 2 * (gaussianDensityEval (x.1 - x.2)).val + 2 * x.2) = _
      rw [gaussianDensityEval_val]
      rfl
  | swish β hβ => rfl
  | sigmoid => rfl
  | softplus θ hθ => rfl

/-- These are counts of the scalar calls in `activation`, not assigned costs
for an opaque activation operator. -/
def activationSteps : ClosedFormActivation → ℕ
  | .relu => 1
  | .gaussianGelu => 15
  | .swish _ _ => 18
  | .sigmoid => 17
  | .softplus _ _ => 7

@[simp] theorem activation_steps (φ : ClosedFormActivation) (x : ℝ × ℝ) :
    (activation φ x).steps = activationSteps φ := by
  cases φ <;> rfl

theorem activation_steps_le (φ : ClosedFormActivation) (x : ℝ × ℝ) :
    (activation φ x).steps ≤ 32 := by
  rw [activation_steps]
  cases φ <;> norm_num [activationSteps]

end HiddenMonotonicity.TransformerDC.SharedCost
