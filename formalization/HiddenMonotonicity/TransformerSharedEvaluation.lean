import HiddenMonotonicity.TransformerPrimitiveCost
import HiddenMonotonicity.TransformerCorrectness

/-! A shared, costed evaluation of the same Transformer DC streams.
Every `gather` materializes a finite vector; subsequent uses are table reads.
Q/K/V are computed once per token, softmax statistics once per row, and LayerNorm
statistics once per token. Arithmetic steps are accumulated by the primitive writer. -/
noncomputable section
set_option autoImplicit false
namespace HiddenMonotonicity.TransformerDC
open scoped BigOperators
open SharedCost (Costed)

/-- Fixed model collections are put in indexed arrays once before their uses. -/
def storedList {α : Type*} (xs : List α) : Vector α xs.length :=
  ⟨xs.toArray, by simp⟩

@[simp] theorem storedList_get {α : Type*} (xs : List α) (i : Fin xs.length) :
    (storedList xs).get i = xs.get i := by
  simp [storedList, Vector.get]

abbrev PairTable (t d : ℕ) := Vector (Vector (ℝ × ℝ) d) t

def sharedAffine {n m : ℕ} (a : TransformerAffine n m)
    (x : Fin n → ℝ × ℝ) : Costed (Vector (ℝ × ℝ) m) := do
  SharedCost.gather fun i : Fin m => do
    let terms ← SharedCost.gather fun j : Fin n => SharedCost.scalePair (a.weight i j) (x j)
    let total ← SharedCost.sumPair terms.get
    let bias ← SharedCost.constPair (a.bias i)
    SharedCost.addPair total bias

def sharedNorm {t d : ℕ} (p : TransformerNorm d)
    (x : Fin t → Fin d → ℝ × ℝ) : Costed (PairTable t d) :=
  SharedCost.gather fun q : Fin t => SharedCost.layerNorm p.epsilon p.gamma p.beta (x q)

def sharedOptionalNorm {t d : ℕ} (p : Option (TransformerNorm d))
    (x : Fin t → Fin d → ℝ × ℝ) : Costed (PairTable t d) :=
  match p with
  | none => SharedCost.gather fun q : Fin t =>
      SharedCost.gather fun i : Fin d => pure (x q i)
  | some norm => sharedNorm norm x

/-- All Q/K/V vectors are cached before processing query rows. A row computes
its score vector and common softmax statistics once, then all value coordinates. -/
def TransformerHead.shared {t d : ℕ} (h : TransformerHead t d)
    (x : Fin t → Fin d → ℝ × ℝ) : Costed (PairTable t d) := do
  let queries ← SharedCost.gather fun q : Fin t => sharedAffine h.query (x q)
  let keys ← SharedCost.gather fun k : Fin t => sharedAffine h.key (x k)
  let values ← SharedCost.gather fun k : Fin t => sharedAffine h.value (x k)
  SharedCost.gather fun q : Fin t => do
    let logits ← SharedCost.gather fun k : Fin (h.mask.keyCount q) => do
      let products ← SharedCost.gather fun r : Fin h.keyWidth =>
        SharedCost.mulPair ((queries.get q).get r) ((keys.get (h.mask.keyAt q k)).get r)
      let dot ← SharedCost.sumPair products.get
      SharedCost.scalePair h.scale dot
    let attention ← SharedCost.softmax logits.get
    let context ← SharedCost.gather fun r : Fin h.valueWidth => do
      let terms ← SharedCost.gather fun k : Fin (h.mask.keyCount q) =>
        SharedCost.mulPair (attention.get k) ((values.get (h.mask.keyAt q k)).get r)
      SharedCost.sumPair terms.get
    SharedCost.gather fun i : Fin d => do
      let terms ← SharedCost.gather fun r : Fin h.valueWidth =>
        SharedCost.scalePair (h.outputWeight i r) (context.get r)
      SharedCost.sumPair terms.get

/-- Normalized inputs, head outputs, both residuals, and feed-forward vectors
are finite stored tables, so later stages never re-evaluate earlier blocks. -/
def TransformerBlock.shared {t d : ℕ} (b : TransformerBlock t d)
    (x : Fin t → Fin d → ℝ × ℝ) : Costed (PairTable t d) := do
  let normalized ← sharedNorm b.attentionNorm x
  let parameters := storedList b.heads
  let heads ← SharedCost.gather fun h : Fin b.heads.length =>
    (parameters.get h).shared (fun q i => (normalized.get q).get i)
  let residual ← SharedCost.gather fun q : Fin t =>
    SharedCost.gather fun i : Fin d => do
      let total ← SharedCost.sumPair (fun h : Fin b.heads.length => ((heads.get h).get q).get i)
      let bias ← SharedCost.constPair (b.attentionBias i)
      let attention ← SharedCost.addPair total bias
      SharedCost.addPair (x q i) attention
  let ffNormalized ← sharedNorm b.feedForwardNorm (fun q i => (residual.get q).get i)
  SharedCost.gather fun q : Fin t => do
    let up ← sharedAffine b.up ((ffNormalized.get q).get)
    let activated ← SharedCost.gather fun j : Fin b.hiddenWidth =>
      SharedCost.activation b.activation (up.get j)
    let down ← sharedAffine b.down activated.get
    SharedCost.gather fun i : Fin d =>
      SharedCost.addPair ((residual.get q).get i) (down.get i)

def sharedBlocks {t d : ℕ} : List (TransformerBlock t d) →
    (Fin t → Fin d → ℝ × ℝ) → Costed (PairTable t d)
  | [], x => SharedCost.gather fun q : Fin t =>
      SharedCost.gather fun i : Fin d => pure (x q i)
  | b :: bs, x => do
      let next ← b.shared x
      sharedBlocks bs (fun q i => (next.get q).get i)

/-- Full shared evaluator, including positional bias, arbitrary finite depth,
optional final normalization and every signed affine output. -/
def Transformer.sharedDecompose {t d o : ℕ} (net : Transformer t d o)
    (x : DoubledInput (Fin t × Fin d)) : Costed (Vector (ℝ × ℝ) o) := do
  let positioned ← SharedCost.gather fun q : Fin t =>
    SharedCost.gather fun j : Fin d => do
      let bias ← SharedCost.constPair (net.positionalBias q j)
      SharedCost.addPair (x.1 (q,j), x.2 (q,j)) bias
  let blocks ← sharedBlocks net.blocks (fun q i => (positioned.get q).get i)
  let normalized ← sharedOptionalNorm net.finalNorm (fun q i => (blocks.get q).get i)
  SharedCost.gather fun i : Fin o => do
    let rows ← SharedCost.gather fun q : Fin t => do
      let terms ← SharedCost.gather fun j : Fin d =>
        SharedCost.scalePair (net.readoutWeight i q j) ((normalized.get q).get j)
      SharedCost.sumPair terms.get
    let total ← SharedCost.sumPair rows.get
    let bias ← SharedCost.constPair (net.readoutBias i)
    SharedCost.addPair total bias


end HiddenMonotonicity.TransformerDC
