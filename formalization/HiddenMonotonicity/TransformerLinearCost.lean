import HiddenMonotonicity.TransformerSharedCorrectness

/-! Arithmetic work of the materialized Transformer DC evaluation.

The reference size counts the scalar nodes of a shared ordinary forward graph.
Real arithmetic, comparisons and standard scalar functions have unit cost;
constants count as one source node. Vector materialization and indexed access are
not arithmetic operations. Softmax and LayerNorm share their row/token reductions.
This is an arithmetic-operation bound, not a bit-complexity or floating-point claim.
-/
noncomputable section
set_option autoImplicit false
namespace HiddenMonotonicity.TransformerDC
open scoped BigOperators

namespace SharedRuntime

/-- Each affine output has `n` scalar products, `n` accumulation additions,
a bias source, and one bias addition. -/
def affineSize (n m : ℕ) : ℕ := m * (2*n + 2)

/-- A shared dot product has one multiplication and one accumulation per term. -/
def dotSize (n : ℕ) : ℕ := 2*n

/-- Exponentials, denominator accumulation, coordinate divisions, and one
normalization source. The shared denominator is computed once for the row. -/
def softmaxSize (n : ℕ) : ℕ := 3*n + 1

/-- Mean and variance reductions, centering and squares, normalization, learned
scale and bias: seven scalar operations per feature and five shared operations. -/
def normSize (n : ℕ) : ℕ := 7*n + 5

/-- Scalar-graph size of one attention head with cached Q, K and V projections. -/
def headSize {t d : ℕ} (h : TransformerHead t d) : ℕ :=
  t * (2 * affineSize d h.keyWidth + affineSize d h.valueWidth) +
    ∑ q : Fin t,
      (h.mask.keyCount q * (dotSize h.keyWidth + 1) +
       softmaxSize (h.mask.keyCount q) +
       h.valueWidth * dotSize (h.mask.keyCount q) +
       d * dotSize h.valueWidth)

/-- Both norms, cached attention heads, two residual merges, and the tokenwise
MLP, with a scalar activation node for each hidden feature. -/
def blockSize {t d : ℕ} (b : TransformerBlock t d) : ℕ :=
  t * normSize d + (b.heads.map headSize).sum +
    t*d*(b.heads.length + 3) + t * normSize d +
    t*(affineSize d b.hiddenWidth + b.hiddenWidth + affineSize b.hiddenWidth d) + t*d

/-- The shared graph adds the work of its blocks; earlier blocks are never
expanded again at later references. -/
def blocksSize {t d : ℕ} : List (TransformerBlock t d) → ℕ
  | [] => 0
  | b :: bs => blockSize b + blocksSize bs

/-- Nested feature/token reductions for each signed affine output. -/
def readoutSize (t d o : ℕ) : ℕ := o*(2*(t*d) + t + 2)

/-- Positional bias, arbitrary finite block depth, optional final norm, and all
output logits. This size counts the original shared graph, not an expression tree. -/
def networkSize {t d o : ℕ} (net : Transformer t d o) : ℕ :=
  2*(t*d) + blocksSize net.blocks +
    (match net.finalNorm with | none => 0 | some _ => t * normSize d) +
    readoutSize t d o


/-- Exact affine pair schedule cost: scaling, accumulation, bias split, and add. -/
def affineWork (n m : ℕ) : ℕ := m*(6*n+5)
def softmaxWork (n : ℕ) : ℕ := 8*n+4
def normWork (n : ℕ) : ℕ := 39*n+18

def headWork {t d : ℕ} (h : TransformerHead t d) : ℕ :=
  t * (2 * affineWork d h.keyWidth + affineWork d h.valueWidth) +
    ∑ q : Fin t,
      (h.mask.keyCount q * (14*h.keyWidth + 4) +
       softmaxWork (h.mask.keyCount q) +
       h.valueWidth * (14*h.mask.keyCount q) + d * (6*h.valueWidth))

/-- All terms count the schedule directly; 32 uniformly bounds each activation. -/
def blockWork {t d : ℕ} (b : TransformerBlock t d) : ℕ :=
  t * normWork d + (b.heads.map headWork).sum +
    t*d*(2*b.heads.length + 7) + t * normWork d +
    t*(affineWork d b.hiddenWidth + 32*b.hiddenWidth + affineWork b.hiddenWidth d) + 2*(t*d)

def blocksWork {t d : ℕ} : List (TransformerBlock t d) → ℕ
  | [] => 0
  | b :: bs => blockWork b + blocksWork bs

def readoutWork (t d o : ℕ) : ℕ := o*(6*(t*d)+2*t+5)

def networkWork {t d o : ℕ} (net : Transformer t d o) : ℕ :=
  5*(t*d) + blocksWork net.blocks +
    (match net.finalNorm with | none => 0 | some _ => t * normWork d) +
    readoutWork t d o

lemma affineWork_le (n m : ℕ) : affineWork n m ≤ 200 * affineSize n m := by
  dsimp [affineWork, affineSize]
  nlinarith

lemma softmaxWork_le (n : ℕ) : softmaxWork n ≤ 200 * softmaxSize n := by
  dsimp [softmaxWork, softmaxSize]
  omega

lemma normWork_le (n : ℕ) : normWork n ≤ 200 * normSize n := by
  dsimp [normWork, normSize]
  omega

lemma headWork_le {t d : ℕ} (h : TransformerHead t d) : headWork h ≤ 200 * headSize h := by
  have hq : (∑ q : Fin t,
      (h.mask.keyCount q * (14*h.keyWidth + 4) +
       softmaxWork (h.mask.keyCount q) +
       h.valueWidth * (14*h.mask.keyCount q) + d * (6*h.valueWidth))) ≤
      ∑ q : Fin t, 200 *
      (h.mask.keyCount q * (dotSize h.keyWidth + 1) +
       softmaxSize (h.mask.keyCount q) +
       h.valueWidth * dotSize (h.mask.keyCount q) + d * dotSize h.valueWidth) := by
    apply Finset.sum_le_sum
    intro q _
    dsimp [dotSize, softmaxWork, softmaxSize]
    nlinarith
  rw [← Finset.mul_sum] at hq
  have hp := Nat.mul_le_mul_left t
    (Nat.add_le_add (Nat.mul_le_mul_left 2 (affineWork_le d h.keyWidth))
      (affineWork_le d h.valueWidth))
  dsimp [headWork, headSize]
  nlinarith

lemma list_heads_work_le {t d : ℕ} (hs : List (TransformerHead t d)) :
    (hs.map headWork).sum ≤ 200 * (hs.map headSize).sum := by
  induction hs with
  | nil => simp
  | cons h hs ih =>
      have hh := headWork_le h
      simp only [List.map_cons, List.sum_cons]
      omega

lemma blockWork_le {t d : ℕ} (b : TransformerBlock t d) :
    blockWork b ≤ 200 * blockSize b := by
  have hn := Nat.mul_le_mul_left t (normWork_le d)
  have hh := list_heads_work_le b.heads
  have hup := Nat.mul_le_mul_left t (affineWork_le d b.hiddenWidth)
  have hdown := Nat.mul_le_mul_left t (affineWork_le b.hiddenWidth d)
  have hres : t*d*(2*b.heads.length+7) ≤ 200*(t*d*(b.heads.length+3)) := by
    calc
      t*d*(2*b.heads.length+7) ≤ t*d*(200*(b.heads.length+3)) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have hact : 32*(t*b.hiddenWidth) ≤ 200*(t*b.hiddenWidth) := by omega
  have hlast : 2*(t*d) ≤ 200*(t*d) := by omega
  dsimp [blockWork, blockSize]
  nlinarith only [hn, hh, hup, hdown, hres, hact, hlast]

lemma blocksWork_le {t d : ℕ} (bs : List (TransformerBlock t d)) :
    blocksWork bs ≤ 200 * blocksSize bs := by
  induction bs with
  | nil => simp [blocksWork, blocksSize]
  | cons b bs ih =>
      have hb := blockWork_le b
      simp only [blocksWork, blocksSize]
      omega

lemma readoutWork_le (t d o : ℕ) : readoutWork t d o ≤ 200 * readoutSize t d o := by
  dsimp [readoutWork, readoutSize]
  calc
    o*(6*(t*d)+2*t+5) ≤ o*(200*(2*(t*d)+t+2)) :=
      Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

lemma networkWork_le {t d o : ℕ} (net : Transformer t d o) :
    networkWork net ≤ 200 * networkSize net := by
  have hb := blocksWork_le net.blocks
  have hr := readoutWork_le t d o
  have hn := Nat.mul_le_mul_left t (normWork_le d)
  dsimp [networkWork, networkSize]
  split <;> nlinarith

end SharedRuntime

open SharedRuntime

@[simp] lemma sum_list_get {α : Type*} (xs : List α) (f : α → ℕ) :
    (∑ i : Fin xs.length, f (xs.get i)) = (xs.map f).sum := by
  rw [← List.sum_ofFn]
  change (List.ofFn (f ∘ xs.get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get]

@[simp] theorem sharedAffine_steps {n m : ℕ} (a : TransformerAffine n m)
    (x : Fin n → ℝ × ℝ) : (sharedAffine a x).steps = affineWork n m := by
  simp [sharedAffine, affineWork]
  omega

@[simp] theorem sharedNorm_steps {t d : ℕ} (p : TransformerNorm d)
    (x : Fin t → Fin d → ℝ × ℝ) : (sharedNorm p x).steps = t * normWork d := by
  simp [sharedNorm, normWork]

@[simp] theorem sharedOptionalNorm_steps {t d : ℕ} (p : Option (TransformerNorm d))
    (x : Fin t → Fin d → ℝ × ℝ) :
    (sharedOptionalNorm p x).steps = (match p with | none => 0 | some _ => t * normWork d) := by
  cases p <;> simp [sharedOptionalNorm]

@[simp] theorem TransformerHead.shared_steps {t d : ℕ} (h : TransformerHead t d)
    (x : Fin t → Fin d → ℝ × ℝ) : (h.shared x).steps = headWork h := by
  simp [TransformerHead.shared, headWork, softmaxWork, Finset.sum_add_distrib]
  ring_nf
  simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

lemma TransformerBlock.shared_steps_le {t d : ℕ} (b : TransformerBlock t d)
    (x : Fin t → Fin d → ℝ × ℝ) : (b.shared x).steps ≤ blockWork b := by
  have ha : SharedCost.activationSteps b.activation ≤ 32 := by
    simpa only [SharedCost.activation_steps] using
      SharedCost.activation_steps_le b.activation (0,0)
  have ht := Nat.mul_le_mul_left (t*b.hiddenWidth) ha
  simp [TransformerBlock.shared, blockWork, SharedCost.activation_steps]
  nlinarith only [ht]

lemma sharedBlocks_steps_le {t d : ℕ} (bs : List (TransformerBlock t d))
    (x : Fin t → Fin d → ℝ × ℝ) : (sharedBlocks bs x).steps ≤ blocksWork bs := by
  induction bs generalizing x with
  | nil => simp [sharedBlocks, blocksWork]
  | cons b bs ih =>
      simp only [sharedBlocks, SharedCost.steps_mbind, blocksWork]
      exact Nat.add_le_add (b.shared_steps_le x) (ih _)

lemma Transformer.sharedDecompose_steps_work {t d o : ℕ} (net : Transformer t d o)
    (x : DoubledInput (Fin t × Fin d)) :
    (net.sharedDecompose x).steps ≤ networkWork net := by
  have hb := sharedBlocks_steps_le net.blocks
  simp [Transformer.sharedDecompose, networkWork, readoutWork]
  nlinarith [hb (fun q j => TransformerDC.addPair (x.1 (q,j),x.2 (q,j))
    (TransformerDC.constPair (net.positionalBias q j)))]

/-- Uniform overhead for the same value-correct materialized evaluator. -/
theorem Transformer.sharedDecompose_steps_le {t d o : ℕ} (net : Transformer t d o)
    (x : DoubledInput (Fin t × Fin d)) :
    (net.sharedDecompose x).steps ≤ 200 * networkSize net :=
  (net.sharedDecompose_steps_work x).trans (networkWork_le net)


/-- The exact same globally defined DC streams admit a shared evaluation with
uniform linear arithmetic cost. The cost statement is proved for the materialized
writer computation, not for the earlier recursive expression-tree evaluator. -/
theorem Transformer.dc_decomposition_linear_cost {t d o : ℕ} (net : Transformer t d o) :
    (∀ x i, (net.sharedDecompose x).val.get i = net.decompose x i) ∧
    (∀ x, (net.sharedDecompose x).steps ≤ 200 * networkSize net) ∧
    MonotoneOn net.decompose (Set.Ici (0 : DoubledInput (Fin t × Fin d))) ∧
    (∀ i, ConvexOn ℝ (Set.Ici (0 : DoubledInput (Fin t × Fin d)))
      (fun x => (net.decompose x i).1)) ∧
    (∀ i, ConvexOn ℝ (Set.Ici (0 : DoubledInput (Fin t × Fin d)))
      (fun x => (net.decompose x i).2)) ∧
    (∀ x, 0 ≤ x → 0 ≤ net.decompose x) ∧
    (∀ x i, (net.decompose x i).1 - (net.decompose x i).2 =
      net.eval (x.1 - x.2) i) ∧
    (∀ i, ConvexOn ℝ Set.univ (fun x : Fin t × Fin d → ℝ =>
      (net.rawDecompose x i).1)) ∧
    (∀ i, ConvexOn ℝ Set.univ (fun x : Fin t × Fin d → ℝ =>
      (net.rawDecompose x i).2)) ∧
    (∀ x, 0 ≤ net.rawDecompose x) ∧
    (∀ x i, (net.rawDecompose x i).1 - (net.rawDecompose x i).2 = net.eval x i) := by
  obtain ⟨hm,hp,hq,hn,he⟩ := net.dc_decomposition
  obtain ⟨hrp,hrq,hrn,hre⟩ := net.raw_dc_decomposition
  exact ⟨net.sharedDecompose_eq,net.sharedDecompose_steps_le,hm,hp,hq,hn,he,hrp,hrq,hrn,hre⟩

end HiddenMonotonicity.TransformerDC
