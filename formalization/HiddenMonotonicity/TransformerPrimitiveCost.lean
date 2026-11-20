import HiddenMonotonicity.TransformerActivationCost

/-! Costed whole-row softmax and LayerNorm. Reductions and shared terms are
materialized before coordinatewise outputs, so no vector statistic is recomputed
for each output. Fixed model/dimension constants are precomputed parameters. -/
noncomputable section
set_option autoImplicit false
namespace HiddenMonotonicity.TransformerDC.SharedCost
open scoped BigOperators

/-- Evaluate both softmax streams for a whole row, sharing exponentials,
denominator, log-sum-exp, and the common negative-stream sum. -/
def softmax {n : ℕ} (xs : Fin n → ℝ × ℝ) : Costed (Vector (ℝ × ℝ) n) := do
  let es ← gather (fun i => do
    let d ← sub (xs i).1 (xs i).2
    exp d)
  let den ← sumFin es.get
  let h ← log den
  let sy ← sumFin (fun i => (xs i).2)
  let common ← add h sy
  let common ← div common 2
  let common ← sub common (SoftmaxDC.softmaxNormalization (Fin n))
  gather (fun i => do
    let pi ← div (es.get i) den
    let half ← div pi 2
    let p ← add common half
    let q ← sub common half
    pure (p,q))

/-- The two branches of the tangent-extended reciprocal square root each
perform two scalar operations; the branch comparison itself is counted. -/
def inverseSqrtPair (ε : ℝ) (p : ℝ × ℝ) : Costed (ℝ × ℝ) := do
  let d ← sub p.1 p.2
  let left ← nonpos d
  let r ← if left then do
      let t ← mul (SmoothDC.inverseSqrtSlope ε) d
      sub (ε ^ (-1/2 : ℝ)) t
    else do
      let t ← add ε d
      rpow t (-1/2)
  let common ← mul (SmoothDC.inverseSqrtSlope ε) p.1
  let first ← add r common
  pure (first,common)

/-- Materialize the centered vector and compute the variance pair and inverse
root only once for all output coordinates. -/
def layerNorm {n : ℕ} (ε : ℝ) (γ β : Fin n → ℝ)
    (xs : Fin n → ℝ × ℝ) : Costed (Vector (ℝ × ℝ) n) := do
  let s ← sumPair xs
  let mean ← scalePair ((n : ℝ)⁻¹) s
  let negativeMean ← scalePair (-1) mean
  let centered ← gather (fun i => addPair (xs i) negativeMean)
  let squares ← gather (fun i => mulPair (centered.get i) (centered.get i))
  let varianceSum ← sumPair squares.get
  let variance ← scalePair ((n : ℝ)⁻¹) varianceSum
  let inverse ← inverseSqrtPair ε variance
  gather (fun i => do
    let normalized ← mulPair (centered.get i) inverse
    let scaled ← scalePair (γ i) normalized
    let bias ← constPair (β i)
    addPair scaled bias)



@[simp] theorem softmax_steps {n : ℕ} (xs : Fin n → ℝ × ℝ) :
    (softmax xs).steps = 8*n+4 := by
  simp [softmax, add, sub, div, exp, log, pure]
  omega


@[simp] theorem inverseSqrtPair_steps (ε : ℝ) (p : ℝ × ℝ) :
    (inverseSqrtPair ε p).steps = 6 := by
  by_cases h : p.1-p.2 ≤ 0 <;>
    simp [inverseSqrtPair, sub, nonpos, mul, add, rpow, pure, h]


@[simp] theorem layerNorm_steps {n : ℕ} (ε : ℝ) (γ β : Fin n → ℝ)
    (xs : Fin n → ℝ × ℝ) :
    (layerNorm ε γ β xs).steps = 39*n+18 := by
  simp [layerNorm]
  omega

end HiddenMonotonicity.TransformerDC.SharedCost
