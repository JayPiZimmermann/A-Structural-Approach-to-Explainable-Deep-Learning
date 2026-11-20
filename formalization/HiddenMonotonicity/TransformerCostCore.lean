import HiddenMonotonicity.TransformerExpr

/-! Unit-cost real-arithmetic computations. A bind executes and caches its left
result once. Gather materializes its finitely many results into a Vector; reads
and fixed parameters are free in this arithmetic-operation model. -/
noncomputable section
set_option autoImplicit false
namespace HiddenMonotonicity.TransformerDC.SharedCost
open scoped BigOperators
universe u

structure Costed (α : Type*) where
  val : α
  steps : ℕ

def pure {α : Type*} (a : α) : Costed α := ⟨a,0⟩
def bind {α β : Type*} (a : Costed α) (f : α → Costed β) : Costed β :=
  let b := f a.val
  ⟨b.val,a.steps+b.steps⟩
instance : Monad Costed where
  pure := pure
  bind := bind

@[simp] theorem val_mpure {α : Type u} (a : α) :
    (Pure.pure a : Costed α).val = a := rfl
@[simp] theorem steps_mpure {α : Type u} (a : α) :
    (Pure.pure a : Costed α).steps = 0 := rfl
@[simp] theorem val_mbind {α β : Type u} (a : Costed α) (f : α → Costed β) :
    (a >>= f).val = (f a.val).val := rfl
@[simp] theorem steps_mbind {α β : Type u} (a : Costed α) (f : α → Costed β) :
    (a >>= f).steps = a.steps+(f a.val).steps := rfl

@[simp] theorem val_pure {α : Type*} (a : α) : (pure a).val = a := rfl
@[simp] theorem steps_pure {α : Type*} (a : α) : (pure a).steps = 0 := rfl
@[simp] theorem val_bind {α β : Type*} (a : Costed α) (f : α → Costed β) :
    (bind a f).val = (f a.val).val := rfl
@[simp] theorem steps_bind {α β : Type*} (a : Costed α) (f : α → Costed β) :
    (bind a f).steps = a.steps+(f a.val).steps := rfl

def gather {α : Type*} {n : ℕ} (f : Fin n → Costed α) : Costed (Vector α n) :=
  let results := Vector.ofFn f
  ⟨results.map Costed.val,∑ i, (results.get i).steps⟩
@[simp] theorem get_val_gather {α : Type*} {n : ℕ} (f : Fin n → Costed α) (i : Fin n) :
    (gather f).val.get i = (f i).val := by
  change (gather f).val[i.val] = (f i).val
  simp [gather]
@[simp] theorem steps_gather {α : Type*} {n : ℕ} (f : Fin n → Costed α) :
    (gather f).steps = ∑ i, (f i).steps := by
  dsimp only [gather]
  apply Finset.sum_congr rfl
  intro i _
  change ((Vector.ofFn f)[i.val]).steps = (f i).steps
  simp

def add (a b : ℝ) : Costed ℝ := ⟨a+b,1⟩
def sub (a b : ℝ) : Costed ℝ := ⟨a-b,1⟩
def mul (a b : ℝ) : Costed ℝ := ⟨a*b,1⟩
def div (a b : ℝ) : Costed ℝ := ⟨a/b,1⟩
def neg (a : ℝ) : Costed ℝ := ⟨-a,1⟩
def inv (a : ℝ) : Costed ℝ := ⟨a⁻¹,1⟩
def exp (a : ℝ) : Costed ℝ := ⟨Real.exp a,1⟩
def log (a : ℝ) : Costed ℝ := ⟨Real.log a,1⟩
def sqrt (a : ℝ) : Costed ℝ := ⟨Real.sqrt a,1⟩
/-- Fixed-power evaluation is a scalar real-arithmetic primitive. -/
def rpow (a p : ℝ) : Costed ℝ := ⟨a^p,1⟩
def max (a b : ℝ) : Costed ℝ := ⟨Max.max a b,1⟩
def cdf (a : ℝ) : Costed ℝ := ⟨SmoothDC.standardGaussianCDF a,1⟩
def nonneg (a : ℝ) : Costed Bool := ⟨decide (0 ≤ a),1⟩
def nonpos (a : ℝ) : Costed Bool := ⟨decide (a ≤ 0),1⟩

@[simp] theorem add_val (a b : ℝ) : (add a b).val = a+b := rfl
@[simp] theorem add_steps (a b : ℝ) : (add a b).steps = 1 := rfl
@[simp] theorem sub_val (a b : ℝ) : (sub a b).val = a-b := rfl
@[simp] theorem sub_steps (a b : ℝ) : (sub a b).steps = 1 := rfl
@[simp] theorem mul_val (a b : ℝ) : (mul a b).val = a*b := rfl
@[simp] theorem mul_steps (a b : ℝ) : (mul a b).steps = 1 := rfl
@[simp] theorem div_val (a b : ℝ) : (div a b).val = a/b := rfl
@[simp] theorem div_steps (a b : ℝ) : (div a b).steps = 1 := rfl
@[simp] theorem max_val (a b : ℝ) : (max a b).val = Max.max a b := rfl
@[simp] theorem max_steps (a b : ℝ) : (max a b).steps = 1 := rfl
@[simp] theorem neg_val (a : ℝ) : (neg a).val = -a := rfl
@[simp] theorem neg_steps (a : ℝ) : (neg a).steps = 1 := rfl
@[simp] theorem inv_val (a : ℝ) : (inv a).val = a⁻¹ := rfl
@[simp] theorem inv_steps (a : ℝ) : (inv a).steps = 1 := rfl
@[simp] theorem exp_val (a : ℝ) : (exp a).val = Real.exp a := rfl
@[simp] theorem exp_steps (a : ℝ) : (exp a).steps = 1 := rfl
@[simp] theorem log_val (a : ℝ) : (log a).val = Real.log a := rfl
@[simp] theorem log_steps (a : ℝ) : (log a).steps = 1 := rfl
@[simp] theorem sqrt_val (a : ℝ) : (sqrt a).val = Real.sqrt a := rfl
@[simp] theorem sqrt_steps (a : ℝ) : (sqrt a).steps = 1 := rfl
@[simp] theorem cdf_val (a : ℝ) : (cdf a).val = SmoothDC.standardGaussianCDF a := rfl
@[simp] theorem cdf_steps (a : ℝ) : (cdf a).steps = 1 := rfl
@[simp] theorem nonneg_val (a : ℝ) : (nonneg a).val = decide (0 ≤ a) := rfl
@[simp] theorem nonneg_steps (a : ℝ) : (nonneg a).steps = 1 := rfl
@[simp] theorem nonpos_val (a : ℝ) : (nonpos a).val = decide (a ≤ 0) := rfl
@[simp] theorem nonpos_steps (a : ℝ) : (nonpos a).steps = 1 := rfl
@[simp] theorem rpow_val (a p : ℝ) : (rpow a p).val = a^p := rfl
@[simp] theorem rpow_steps (a p : ℝ) : (rpow a p).steps = 1 := rfl

/-- A sum performs one addition for each list entry, starting at zero. -/
def sumList : List ℝ → Costed ℝ
  | [] => pure 0
  | a::as => do
      let s ← sumList as
      add a s
@[simp] theorem sumList_val (xs : List ℝ) : (sumList xs).val = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [sumList, bind, add, pure] using congrArg (fun s => x+s) ih
@[simp] theorem sumList_steps (xs : List ℝ) : (sumList xs).steps = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [sumList, add, pure] using ih

def sumFin {n : ℕ} (xs : Fin n → ℝ) : Costed ℝ := sumList (List.ofFn xs)
@[simp] theorem sumFin_val {n : ℕ} (xs : Fin n → ℝ) : (sumFin xs).val = ∑ i, xs i := by
  simp [sumFin, List.sum_ofFn]
@[simp] theorem sumFin_steps {n : ℕ} (xs : Fin n → ℝ) : (sumFin xs).steps = n := by
  simp [sumFin]

def constPair (c : ℝ) : Costed (ℝ × ℝ) := do
  let nc ← neg c
  let p ← max c 0
  let q ← max nc 0
  pure (p,q)
def addPair (p q : ℝ × ℝ) : Costed (ℝ × ℝ) := do
  let a ← add p.1 q.1
  let b ← add p.2 q.2
  pure (a,b)
def scalePair (c : ℝ) (p : ℝ × ℝ) : Costed (ℝ × ℝ) := do
  let nc ← neg c
  let pos ← nonneg c
  let a ← mul (if pos then c else nc) (if pos then p.1 else p.2)
  let b ← mul (if pos then c else nc) (if pos then p.2 else p.1)
  pure (a,b)
def mulPair (p q : ℝ × ℝ) : Costed (ℝ × ℝ) := do
  let a ← add p.1 q.1
  let b ← add p.2 q.2
  let c ← add p.1 q.2
  let d ← add p.2 q.1
  let aa ← mul a a
  let bb ← mul b b
  let cc ← mul c c
  let dd ← mul d d
  let plus ← add aa bb
  let minus ← add cc dd
  let plus ← div plus 2
  let minus ← div minus 2
  pure (plus,minus)
def sumPair {n : ℕ} (xs : Fin n → ℝ × ℝ) : Costed (ℝ × ℝ) := do
  let a ← sumFin (fun i => (xs i).1)
  let b ← sumFin (fun i => (xs i).2)
  pure (a,b)

@[simp] theorem constPair_val (c : ℝ) : (constPair c).val = TransformerDC.constPair c := rfl
@[simp] theorem constPair_steps (c : ℝ) : (constPair c).steps = 3 := rfl
@[simp] theorem addPair_val (p q : ℝ × ℝ) : (addPair p q).val = TransformerDC.addPair p q := rfl
@[simp] theorem addPair_steps (p q : ℝ × ℝ) : (addPair p q).steps = 2 := rfl
@[simp] theorem scalePair_val (c : ℝ) (p : ℝ × ℝ) :
    (scalePair c p).val = TransformerDC.scalePair c p := by
  by_cases h : 0 ≤ c <;> simp [scalePair, pure, neg, nonneg, mul, TransformerDC.scalePair, h]
@[simp] theorem scalePair_steps (c : ℝ) (p : ℝ × ℝ) : (scalePair c p).steps = 4 := rfl
@[simp] theorem mulPair_val (p q : ℝ × ℝ) :
    (mulPair p q).val = TransformerDC.mulPair p q := by
  apply Prod.ext <;> simp [mulPair, pure, add, mul, div, TransformerDC.mulPair,
    productSplit, pow_two]
@[simp] theorem mulPair_steps (p q : ℝ × ℝ) : (mulPair p q).steps = 12 := rfl
@[simp] theorem sumPair_val {n : ℕ} (xs : Fin n → ℝ × ℝ) :
    (sumPair xs).val = ∑ i, xs i := by
  apply Prod.ext <;> simp [sumPair, pure, Prod.fst_sum, Prod.snd_sum]
@[simp] theorem sumPair_steps {n : ℕ} (xs : Fin n → ℝ × ℝ) :
    (sumPair xs).steps = 2*n := by
  simp [sumPair, pure, two_mul]

end HiddenMonotonicity.TransformerDC.SharedCost
