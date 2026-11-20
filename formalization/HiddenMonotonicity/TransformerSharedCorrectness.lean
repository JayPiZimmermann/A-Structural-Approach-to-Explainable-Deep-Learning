import HiddenMonotonicity.TransformerSharedEvaluation
import HiddenMonotonicity.TransformerPrimitiveCorrectness

/-! The shared schedule computes exactly the previously verified DC pair. -/
noncomputable section
set_option autoImplicit false
namespace HiddenMonotonicity.TransformerDC
open scoped BigOperators

universe u

@[simp] theorem sharedAffine_compile {n m : ℕ} {ι : Type u}
    (a : TransformerAffine n m) (x : Fin n → Expr ι) (v : ι → ℝ × ℝ) (i : Fin m) :
    (sharedAffine a (fun j => (x j).splitEval v)).val.get i =
      (a.compile x i).splitEval v := by
  simp [sharedAffine, TransformerAffine.compile, Expr.splitEval]

@[simp] theorem sharedNorm_compile {t d : ℕ} {ι : Type u}
    (p : TransformerNorm d) (x : Fin t → Fin d → Expr ι)
    (v : ι → ℝ × ℝ) (q : Fin t) (i : Fin d) :
    ((sharedNorm p (fun a b => (x a b).splitEval v)).val.get q).get i =
      (p.compile x q i).splitEval v := by
  simp [sharedNorm, TransformerNorm.compile, Expr.splitEval]

@[simp] theorem sharedOptionalNorm_compile {t d : ℕ} {ι : Type u}
    (p : Option (TransformerNorm d)) (x : Fin t → Fin d → Expr ι)
    (v : ι → ℝ × ℝ) (q : Fin t) (i : Fin d) :
    ((sharedOptionalNorm p (fun a b => (x a b).splitEval v)).val.get q).get i =
      (compileOptionalTransformerNorm p x q i).splitEval v := by
  cases p <;> simp [sharedOptionalNorm, compileOptionalTransformerNorm]

@[simp] theorem TransformerHead.shared_compile {t d : ℕ} {ι : Type u}
    (h : TransformerHead t d) (x : Fin t → Fin d → Expr ι)
    (v : ι → ℝ × ℝ) (q : Fin t) (i : Fin d) :
    ((h.shared (fun a b => (x a b).splitEval v)).val.get q).get i =
      (h.compile x q i).splitEval v := by
  let xp := fun q r => (x q r).splitEval v
  let queries := (SharedCost.gather fun q : Fin t => sharedAffine h.query (xp q)).val
  let keys := (SharedCost.gather fun k : Fin t => sharedAffine h.key (xp k)).val
  let values := (SharedCost.gather fun k : Fin t => sharedAffine h.value (xp k)).val
  have hqueries (q : Fin t) (r : Fin h.keyWidth) :
      (queries.get q).get r = (h.query.compile (x q) r).splitEval v := by
    simp only [queries, SharedCost.get_val_gather]
    exact sharedAffine_compile h.query (x q) v r
  have hkeys (k : Fin t) (r : Fin h.keyWidth) :
      (keys.get k).get r = (h.key.compile (x k) r).splitEval v := by
    simp only [keys, SharedCost.get_val_gather]
    exact sharedAffine_compile h.key (x k) v r
  have hvalues (k : Fin t) (r : Fin h.valueWidth) :
      (values.get k).get r = (h.value.compile (x k) r).splitEval v := by
    simp only [values, SharedCost.get_val_gather]
    exact sharedAffine_compile h.value (x k) v r
  let logits := (SharedCost.gather fun k : Fin (h.mask.keyCount q) => do
      let products ← SharedCost.gather fun r : Fin h.keyWidth =>
        SharedCost.mulPair ((queries.get q).get r) ((keys.get (h.mask.keyAt q k)).get r)
      let dot ← SharedCost.sumPair products.get
      SharedCost.scalePair h.scale dot).val
  have hlogits (k : Fin (h.mask.keyCount q)) :
      logits.get k = (h.compileLogits x q k).splitEval v := by
    simp only [logits, SharedCost.get_val_gather, SharedCost.val_mbind,
      SharedCost.sumPair_val, SharedCost.scalePair_val, SharedCost.mulPair_val,
      hqueries, hkeys, TransformerHead.compileLogits, Expr.splitEval]
  let attention := (SharedCost.softmax logits.get).val
  have hattention (k : Fin (h.mask.keyCount q)) :
      attention.get k = (Expr.softmax (h.mask.keyCount q) (h.compileLogits x q) k).splitEval v := by
    simp only [attention, SharedCost.softmax_val, hlogits, Expr.splitEval]
  let context := (SharedCost.gather fun r : Fin h.valueWidth => do
      let terms ← SharedCost.gather fun k : Fin (h.mask.keyCount q) =>
        SharedCost.mulPair (attention.get k) ((values.get (h.mask.keyAt q k)).get r)
      SharedCost.sumPair terms.get).val
  have hcontext (r : Fin h.valueWidth) :
      context.get r = (Expr.sum (h.mask.keyCount q) fun k =>
        Expr.mul (Expr.softmax (h.mask.keyCount q) (h.compileLogits x q) k)
          (h.value.compile (x (h.mask.keyAt q k)) r)).splitEval v := by
    simp only [context, SharedCost.get_val_gather, SharedCost.val_mbind,
      SharedCost.sumPair_val, SharedCost.mulPair_val, hattention, hvalues, Expr.splitEval]
  simp only [TransformerHead.shared, SharedCost.val_mbind]
  rw [SharedCost.get_val_gather]
  simp only [SharedCost.val_mbind]
  change (SharedCost.gather fun j : Fin d => do
      let terms ← SharedCost.gather fun r : Fin h.valueWidth =>
        SharedCost.scalePair (h.outputWeight j r) (context.get r)
      SharedCost.sumPair terms.get).val.get i = _
  simp only [SharedCost.get_val_gather, SharedCost.val_mbind, SharedCost.sumPair_val,
    SharedCost.scalePair_val, hcontext, TransformerHead.compile, Expr.splitEval]

@[simp] theorem TransformerBlock.shared_compile {t d : ℕ} {ι : Type u}
    (b : TransformerBlock t d) (x : Fin t → Fin d → Expr ι)
    (v : ι → ℝ × ℝ) (q : Fin t) (i : Fin d) :
    ((b.shared (fun a c => (x a c).splitEval v)).val.get q).get i =
      (b.compile x q i).splitEval v := by
  let xp := fun q j => (x q j).splitEval v
  let normalized := (sharedNorm b.attentionNorm xp).val
  have hnorm (q : Fin t) (j : Fin d) :
      (normalized.get q).get j = (b.attentionNorm.compile x q j).splitEval v :=
    sharedNorm_compile b.attentionNorm x v q j
  have hnormFun : (fun q j => (normalized.get q).get j) =
      fun q j => (b.attentionNorm.compile x q j).splitEval v := by
    funext q j
    exact hnorm q j
  let heads := (SharedCost.gather fun h : Fin b.heads.length =>
    ((storedList b.heads).get h).shared (fun q j => (normalized.get q).get j)).val
  have hheads (h : Fin b.heads.length) (q : Fin t) (j : Fin d) :
      ((heads.get h).get q).get j =
        ((b.heads.get h).compile (b.attentionNorm.compile x) q j).splitEval v := by
    simp only [heads, SharedCost.get_val_gather, storedList_get, hnormFun]
    exact TransformerHead.shared_compile (b.heads.get h) (b.attentionNorm.compile x) v q j
  let residual := (SharedCost.gather fun q : Fin t =>
    SharedCost.gather fun j : Fin d => do
      let total ← SharedCost.sumPair (fun h : Fin b.heads.length => ((heads.get h).get q).get j)
      let bias ← SharedCost.constPair (b.attentionBias j)
      let attention ← SharedCost.addPair total bias
      SharedCost.addPair (xp q j) attention).val
  have hres (q : Fin t) (j : Fin d) :
      (residual.get q).get j = (b.compileAttentionResidual x q j).splitEval v := by
    simp only [residual, SharedCost.get_val_gather, SharedCost.val_mbind,
      SharedCost.sumPair_val, SharedCost.constPair_val, SharedCost.addPair_val,
      hheads, TransformerBlock.compileAttentionResidual, Expr.splitEval]
    rfl
  have hresFun : (fun q j => (residual.get q).get j) =
      fun q j => (b.compileAttentionResidual x q j).splitEval v := by
    funext q j
    exact hres q j
  let ffNormalized := (sharedNorm b.feedForwardNorm (fun q j => (residual.get q).get j)).val
  have hff (q : Fin t) (j : Fin d) :
      (ffNormalized.get q).get j =
        (b.feedForwardNorm.compile (b.compileAttentionResidual x) q j).splitEval v := by
    simp only [ffNormalized, hresFun]
    exact sharedNorm_compile b.feedForwardNorm (b.compileAttentionResidual x) v q j
  have hffFun : (ffNormalized.get q).get =
      fun j => (b.feedForwardNorm.compile (b.compileAttentionResidual x) q j).splitEval v := by
    funext j
    exact hff q j
  let up := (sharedAffine b.up (ffNormalized.get q).get).val
  have hup (j : Fin b.hiddenWidth) : up.get j =
      (b.up.compile (b.feedForwardNorm.compile (b.compileAttentionResidual x) q) j).splitEval v := by
    simp only [up, hffFun]
    exact sharedAffine_compile b.up (b.feedForwardNorm.compile (b.compileAttentionResidual x) q) v j
  let activated := (SharedCost.gather fun j : Fin b.hiddenWidth =>
    SharedCost.activation b.activation (up.get j)).val
  have hact (j : Fin b.hiddenWidth) : activated.get j =
      (Expr.activation b.activation
        (b.up.compile (b.feedForwardNorm.compile (b.compileAttentionResidual x) q) j)).splitEval v := by
    simp only [activated, SharedCost.get_val_gather, SharedCost.activation_val, hup, Expr.splitEval]
  have hactFun : activated.get = fun j =>
      (Expr.activation b.activation
        (b.up.compile (b.feedForwardNorm.compile (b.compileAttentionResidual x) q) j)).splitEval v := by
    funext j
    exact hact j
  let down := (sharedAffine b.down activated.get).val
  have hdown (j : Fin d) : down.get j =
      (b.down.compile (fun r => Expr.activation b.activation
        (b.up.compile (b.feedForwardNorm.compile (b.compileAttentionResidual x) q) r)) j).splitEval v := by
    simp only [down, hactFun]
    exact sharedAffine_compile b.down _ v j
  simp only [TransformerBlock.shared, SharedCost.val_mbind]
  rw [SharedCost.get_val_gather]
  simp only [SharedCost.val_mbind]
  change (SharedCost.gather fun j : Fin d =>
    SharedCost.addPair ((residual.get q).get j) (down.get j)).val.get i = _
  simp only [SharedCost.get_val_gather, SharedCost.addPair_val, hres, hdown,
    TransformerBlock.compile, Expr.splitEval]

@[simp] theorem sharedBlocks_compile {t d : ℕ} {ι : Type u}
    (bs : List (TransformerBlock t d)) (x : Fin t → Fin d → Expr ι)
    (v : ι → ℝ × ℝ) (q : Fin t) (i : Fin d) :
    ((sharedBlocks bs (fun a c => (x a c).splitEval v)).val.get q).get i =
      (compileTransformerBlocks bs x q i).splitEval v := by
  induction bs generalizing x with
  | nil => simp only [sharedBlocks, compileTransformerBlocks,
      SharedCost.get_val_gather, SharedCost.val_mpure]
  | cons b bs ih =>
      simpa only [sharedBlocks, compileTransformerBlocks, SharedCost.val_mbind,
        TransformerBlock.shared_compile] using ih (b.compile x)

set_option maxHeartbeats 2000000 in
/-- The shared costed execution computes precisely the already verified pair,
not merely another pair having the same signed difference. -/
theorem Transformer.sharedDecompose_eq {t d o : ℕ} (net : Transformer t d o)
    (x : DoubledInput (Fin t × Fin d)) (i : Fin o) :
    (net.sharedDecompose x).val.get i = net.decompose x i := by
  let env := fun p : Fin t × Fin d => (x.1 p, x.2 p)
  let positionedExpr := fun q j => (Expr.input (q,j)).add (Expr.const (net.positionalBias q j))
  let blocksExpr := compileTransformerBlocks net.blocks positionedExpr
  let normalizedExpr := compileOptionalTransformerNorm net.finalNorm blocksExpr
  let positioned := (SharedCost.gather fun q : Fin t =>
    SharedCost.gather fun j : Fin d => do
      let bias ← SharedCost.constPair (net.positionalBias q j)
      SharedCost.addPair (x.1 (q,j), x.2 (q,j)) bias).val
  have hpos (q : Fin t) (j : Fin d) : (positioned.get q).get j =
      (positionedExpr q j).splitEval env := by
    simp only [positioned, SharedCost.get_val_gather, SharedCost.val_mbind,
      SharedCost.constPair_val, SharedCost.addPair_val]
    rfl
  have hposFun : (fun q j => (positioned.get q).get j) =
      fun q j => (positionedExpr q j).splitEval env := by
    funext q j
    exact hpos q j
  let blocks := (sharedBlocks net.blocks (fun q j => (positioned.get q).get j)).val
  have hblocks (q : Fin t) (j : Fin d) : (blocks.get q).get j =
      (blocksExpr q j).splitEval env := by
    simp only [blocks, hposFun]
    exact sharedBlocks_compile net.blocks positionedExpr env q j
  have hblocksFun : (fun q j => (blocks.get q).get j) =
      fun q j => (blocksExpr q j).splitEval env := by
    funext q j
    exact hblocks q j
  let normalized := (sharedOptionalNorm net.finalNorm (fun q j => (blocks.get q).get j)).val
  have hnorm (q : Fin t) (j : Fin d) : (normalized.get q).get j =
      (normalizedExpr q j).splitEval env := by
    simp only [normalized, hblocksFun]
    exact sharedOptionalNorm_compile net.finalNorm blocksExpr env q j
  let rows := (SharedCost.gather fun q : Fin t => do
    let terms ← SharedCost.gather fun j : Fin d =>
      SharedCost.scalePair (net.readoutWeight i q j) ((normalized.get q).get j)
    SharedCost.sumPair terms.get).val
  have hrows (q : Fin t) : rows.get q =
      (Expr.sum d fun j => Expr.scale (net.readoutWeight i q j) (normalizedExpr q j)).splitEval env := by
    simp only [rows, SharedCost.get_val_gather, SharedCost.val_mbind,
      SharedCost.sumPair_val, SharedCost.scalePair_val, hnorm, Expr.splitEval]
  simp only [Transformer.sharedDecompose, SharedCost.val_mbind]
  rw [SharedCost.get_val_gather]
  simp only [SharedCost.val_mbind]
  change (SharedCost.addPair (SharedCost.sumPair rows.get).val
    (SharedCost.constPair (net.readoutBias i)).val).val = _
  simp only [SharedCost.addPair_val, SharedCost.sumPair_val, SharedCost.constPair_val, hrows]
  rfl

end HiddenMonotonicity.TransformerDC
