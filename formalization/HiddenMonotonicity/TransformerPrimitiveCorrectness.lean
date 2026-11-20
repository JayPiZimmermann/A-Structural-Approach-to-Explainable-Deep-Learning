import HiddenMonotonicity.TransformerPrimitiveCost
noncomputable section
set_option autoImplicit false
namespace HiddenMonotonicity.TransformerDC.SharedCost
open scoped BigOperators

@[simp] theorem softmax_val {n : ℕ} (xs : Fin n → ℝ × ℝ) (i : Fin n) :
    (softmax xs).val.get i =
      (SoftmaxDC.softmaxSplitFirst i ((fun j => (xs j).1),fun j => (xs j).2),
       SoftmaxDC.softmaxSplitSecond i ((fun j => (xs j).1),fun j => (xs j).2)) := by
  let es : Vector ℝ n := (gather (fun j : Fin n => do
    let d ← sub (xs j).1 (xs j).2
    exp d)).val
  let den := (sumFin es.get).val
  let sy := (sumFin (fun j => (xs j).2)).val
  let common := (Real.log den + sy)/2 - SoftmaxDC.softmaxNormalization (Fin n)
  change (gather (fun j : Fin n => do
    let pi ← div (es.get j) den
    let half ← div pi 2
    let p ← add common half
    let q ← sub common half
    pure (p,q))).val.get i = _
  simp only [get_val_gather, val_mbind, val_pure, div_val, add_val, sub_val]
  have hes (j : Fin n) : es.get j = Real.exp ((xs j).1-(xs j).2) := by
    change (gather (fun k : Fin n => do
      let d ← sub (xs k).1 (xs k).2
      exp d)).val.get j = _
    simp only [get_val_gather, val_mbind, sub_val, exp_val]
  have hd : den = ∑ j, Real.exp ((xs j).1-(xs j).2) := by
    simp only [den, sumFin_val, hes]
  have hy : sy = ∑ j, (xs j).2 := sumFin_val _
  dsimp only [common]
  rw [hd, hy, hes, SoftmaxDC.softmaxSplitFirst_formula,
    SoftmaxDC.softmaxSplitSecond_formula]
  apply Prod.ext <;> dsimp only [SoftmaxDC.softmaxNormalization] <;> ring


@[simp] theorem inverseSqrtPair_val (ε : ℝ) (p : ℝ × ℝ) :
    (inverseSqrtPair ε p).val = SmoothDC.inverseSqrtPair ε p := by
  by_cases h : p.1-p.2 ≤ 0 <;>
    simp [inverseSqrtPair, sub, nonpos, mul, add, rpow, pure,
      SmoothDC.inverseSqrtPair, SmoothDC.inverseSqrtExtension, h]


@[simp] theorem layerNorm_val {n : ℕ} (ε : ℝ) (γ β : Fin n → ℝ)
    (xs : Fin n → ℝ × ℝ) (i : Fin n) :
    (layerNorm ε γ β xs).val.get i = TransformerDC.layerNormPair ε γ β xs i := by
  let mean := (scalePair ((n : ℝ)⁻¹) (sumPair xs).val).val
  let negativeMean := (scalePair (-1) mean).val
  let centered := (gather (fun j : Fin n => addPair (xs j) negativeMean)).val
  let squares := (gather (fun j : Fin n => mulPair (centered.get j) (centered.get j))).val
  let variance := (scalePair ((n : ℝ)⁻¹) (sumPair squares.get).val).val
  let inverse := (inverseSqrtPair ε variance).val
  change (gather (fun j : Fin n => do
    let normalized ← mulPair (centered.get j) inverse
    let scaled ← scalePair (γ j) normalized
    let bias ← constPair (β j)
    addPair scaled bias)).val.get i = _
  simp only [get_val_gather, val_mbind, mulPair_val, scalePair_val,
    constPair_val, addPair_val]
  have hm : mean = TransformerDC.meanPair xs := by
    simp only [mean, scalePair_val, sumPair_val]
    rfl
  have hn : negativeMean = TransformerDC.scalePair (-1) (TransformerDC.meanPair xs) := by
    simp only [negativeMean, scalePair_val, hm]
  have hc (j : Fin n) : centered.get j = TransformerDC.centeredPair xs j := by
    simp only [centered, get_val_gather, addPair_val, hn]
    rfl
  have hs (j : Fin n) : squares.get j =
      TransformerDC.mulPair (TransformerDC.centeredPair xs j)
        (TransformerDC.centeredPair xs j) := by
    simp only [squares, get_val_gather, mulPair_val, hc]
  have hv : variance = TransformerDC.variancePair xs := by
    simp only [variance, scalePair_val, sumPair_val, hs]
    rfl
  have hi : inverse = SmoothDC.inverseSqrtPair ε (TransformerDC.variancePair xs) := by
    simp only [inverse, inverseSqrtPair_val, hv]
  rw [hc, hi]
  rfl

end HiddenMonotonicity.TransformerDC.SharedCost
