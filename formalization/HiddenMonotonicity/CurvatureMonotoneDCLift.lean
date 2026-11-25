import HiddenMonotonicity.MonotoneDCLift
import HiddenMonotonicity.SmoothCurvatureSplit
import HiddenMonotonicity.Decomposition

/-! An asymmetric monotone DC lift built from the actual Jordan curvature
primitives.  Its common coefficient is an explicit total-curvature integral.
The established symmetric lift remains available as a separate construction. -/

namespace HiddenMonotonicity.SmoothDC
open Set Filter MeasureTheory
open scoped Topology

noncomputable def totalPositiveCurvature (f : ℝ → ℝ) : ℝ :=
  ∫ t, positiveCurvature f t

noncomputable def totalNegativeCurvature (f : ℝ → ℝ) : ℝ :=
  ∫ t, negativeCurvature f t

noncomputable def curvatureSlopeShift (f : ℝ → ℝ) : ℝ :=
  max (-minusInfinitySlope f) 0

noncomputable def curvatureLiftWidth (f : ℝ → ℝ) : ℝ :=
  max (minusInfinitySlope f + curvatureSlopeShift f + totalPositiveCurvature f)
    (curvatureSlopeShift f + totalNegativeCurvature f)

noncomputable def curvaturePositiveProfile (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  C1 f x + curvatureSlopeShift f * x

noncomputable def curvatureNegativeProfile (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  C2 f x + curvatureSlopeShift f * x

noncomputable def curvatureLiftPair (f : ℝ → ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (asymmetricLift (curvaturePositiveProfile f) (curvatureLiftWidth f) z,
   asymmetricLift (curvatureNegativeProfile f) (curvatureLiftWidth f) z)

theorem positiveCurvature_eq_absolute (f : ℝ → ℝ) (x : ℝ) :
    positiveCurvature f x = (|curvature f x| + curvature f x) / 2 := by
  rcases le_total (curvature f x) 0 with h | h
  · simp [positiveCurvature, max_eq_right h, abs_of_nonpos h]
  · rw [abs_of_nonneg h]
    simp only [positiveCurvature, max_eq_left h]
    ring

theorem negativeCurvature_eq_absolute (f : ℝ → ℝ) (x : ℝ) :
    negativeCurvature f x = (|curvature f x| - curvature f x) / 2 := by
  rcases le_total (curvature f x) 0 with h | h
  · rw [abs_of_nonpos h]
    simp only [negativeCurvature, max_eq_left (neg_nonneg.mpr h)]
    ring
  · simp [negativeCurvature, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h]

/-- The total curvature used by the construction is exactly the integral of
the absolute second derivative, rather than an unrelated envelope. -/
theorem total_curvature_eq_absolute (f : ℝ → ℝ) (hq : Integrable (curvature f)) :
    totalPositiveCurvature f + totalNegativeCurvature f = ∫ t, |curvature f t| := by
  unfold totalPositiveCurvature totalNegativeCurvature
  rw [← integral_add (positiveCurvature_integrable f hq)
    (negativeCurvature_integrable f hq)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    dsimp only
    rw [positiveCurvature_eq_absolute, negativeCurvature_eq_absolute]
    ring)

theorem curvatureSlopeShift_nonneg (f : ℝ → ℝ) : 0 ≤ curvatureSlopeShift f :=
  le_max_right _ _

theorem totalPositiveCurvature_nonneg (f : ℝ → ℝ) :
    0 ≤ totalPositiveCurvature f := by
  exact integral_nonneg (fun t => le_max_right (curvature f t) 0)

theorem totalNegativeCurvature_nonneg (f : ℝ → ℝ) :
    0 ≤ totalNegativeCurvature f := by
  exact integral_nonneg (fun t => le_max_right (-curvature f t) 0)

theorem curvatureLiftWidth_nonneg (f : ℝ → ℝ) : 0 ≤ curvatureLiftWidth f := by
  exact le_trans (add_nonneg (curvatureSlopeShift_nonneg f)
    (totalNegativeCurvature_nonneg f)) (le_max_right _ _)

/-- The integrated positive and negative curvature yield nonnegative bounded
slopes after the same linear shift. -/
theorem curvature_profile_slope_bounds (f : ℝ → ℝ) (hq : Integrable (curvature f))
    (x : ℝ) :
    (0 ≤ D1 f x + curvatureSlopeShift f ∧
      D1 f x + curvatureSlopeShift f ≤ curvatureLiftWidth f) ∧
    (0 ≤ D2 f x + curvatureSlopeShift f ∧
      D2 f x + curvatureSlopeShift f ≤ curvatureLiftWidth f) := by
  have hp0 : 0 ≤ cumulative (positiveCurvature f) x := by
    exact integral_nonneg (fun t => le_max_right (curvature f t) 0)
  have hn0 : 0 ≤ cumulative (negativeCurvature f) x := by
    exact integral_nonneg (fun t => le_max_right (-curvature f t) 0)
  have hp : cumulative (positiveCurvature f) x ≤ totalPositiveCurvature f := by
    exact setIntegral_le_integral (positiveCurvature_integrable f hq)
      (Eventually.of_forall (fun t => le_max_right (curvature f t) 0))
  have hn : cumulative (negativeCurvature f) x ≤ totalNegativeCurvature f := by
    exact setIntegral_le_integral (negativeCurvature_integrable f hq)
      (Eventually.of_forall (fun t => le_max_right (-curvature f t) 0))
  have hs : -minusInfinitySlope f ≤ curvatureSlopeShift f := le_max_left _ _
  have ha := curvatureSlopeShift_nonneg f
  have hwp : minusInfinitySlope f + curvatureSlopeShift f + totalPositiveCurvature f ≤
      curvatureLiftWidth f := le_max_left _ _
  have hwn : curvatureSlopeShift f + totalNegativeCurvature f ≤ curvatureLiftWidth f :=
    le_max_right _ _
  dsimp [D1, D2, slope]
  constructor <;> constructor <;> linarith

theorem curvaturePositiveProfile_hasDerivAt (f : ℝ → ℝ)
    (hq : Integrable (curvature f)) (x : ℝ) :
    HasDerivAt (curvaturePositiveProfile f) (D1 f x + curvatureSlopeShift f) x := by
  have h := (C1_hasDerivAt f hq x).fun_add
    ((hasDerivAt_id x).const_mul (curvatureSlopeShift f))
  convert h using 1
  · funext t
    simp [curvaturePositiveProfile, id_eq]
  · ring

theorem curvatureNegativeProfile_hasDerivAt (f : ℝ → ℝ)
    (hq : Integrable (curvature f)) (x : ℝ) :
    HasDerivAt (curvatureNegativeProfile f) (D2 f x + curvatureSlopeShift f) x := by
  have h := (C2_hasDerivAt f hq x).fun_add
    ((hasDerivAt_id x).const_mul (curvatureSlopeShift f))
  convert h using 1
  · funext t
    simp [curvatureNegativeProfile, id_eq]
  · ring

theorem curvaturePositiveProfile_convex (f : ℝ → ℝ)
    (hq : Integrable (curvature f)) : ConvexOn ℝ univ (curvaturePositiveProfile f) := by
  have hc : ConvexOn ℝ univ (C1 f) :=
    primitive_convex _ (positiveCurvature_integrable f hq) (fun x => le_max_right _ _) _ _
  constructor
  · exact convex_univ
  · intro x hx y hy a b ha hb hab
    have h := hc.2 hx hy ha hb hab
    simp only [smul_eq_mul] at h ⊢
    dsimp [curvaturePositiveProfile]
    nlinarith only [h]

theorem curvatureNegativeProfile_convex (f : ℝ → ℝ)
    (hq : Integrable (curvature f)) : ConvexOn ℝ univ (curvatureNegativeProfile f) := by
  have hc : ConvexOn ℝ univ (C2 f) :=
    primitive_convex _ (negativeCurvature_integrable f hq) (fun x => le_max_right _ _) _ _
  constructor
  · exact convex_univ
  · intro x hx y hy a b ha hb hab
    have h := hc.2 hx hy ha hb hab
    simp only [smul_eq_mul] at h ⊢
    dsimp [curvatureNegativeProfile]
    nlinarith only [h]

theorem curvature_profile_difference (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)) (x : ℝ) :
    curvaturePositiveProfile f x - curvatureNegativeProfile f x = f x := by
  have h := primitive_difference f hf hAC hq x
  dsimp [curvaturePositiveProfile, curvatureNegativeProfile]
  linarith

/-- The actual curvature construction provides a convex, coordinatewise
nondecreasing pair on all of ℝ², not just on the nonnegative quadrant. -/
theorem curvature_monotone_dc_split (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)) :
    ConvexOn ℝ univ (fun z => (curvatureLiftPair f z).1) ∧
    ConvexOn ℝ univ (fun z => (curvatureLiftPair f z).2) ∧
    Monotone (fun z => (curvatureLiftPair f z).1) ∧
    Monotone (fun z => (curvatureLiftPair f z).2) ∧
    ValidPairActivation f (curvatureLiftPair f) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact asymmetricLift_convex _ _ (curvaturePositiveProfile_convex f hq)
  · exact asymmetricLift_convex _ _ (curvatureNegativeProfile_convex f hq)
  · exact asymmetricLift_monotone _ _ (curvaturePositiveProfile_hasDerivAt f hq) _
      (fun x => (curvature_profile_slope_bounds f hq x).1)
  · exact asymmetricLift_monotone _ _ (curvatureNegativeProfile_hasDerivAt f hq) _
      (fun x => (curvature_profile_slope_bounds f hq x).2)
  · intro x y
    have h := curvature_profile_difference f hf hAC hq (x-y)
    dsimp [curvatureLiftPair, asymmetricLift]
    linarith

/-- Normalization at the origin is sufficient for nonnegative stream outputs
on nonnegative stream inputs. -/
theorem curvatureLiftPair_nonnegative (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)) (hzero : 0 ≤ f 0) :
    NonnegativePairActivation (curvatureLiftPair f) := by
  intro a b ha hb
  have hs := curvature_monotone_dc_split f hf hAC hq
  have hg := hs.2.2.1 (show ((0,0) : ℝ × ℝ) ≤ (a,b) from ⟨ha,hb⟩)
  have hh := hs.2.2.2.1 (show ((0,0) : ℝ × ℝ) ≤ (a,b) from ⟨ha,hb⟩)
  have hg0 : (curvatureLiftPair f (0,0)).1 = f 0 := by
    simp [curvatureLiftPair, asymmetricLift, curvaturePositiveProfile, C1, primitive]
  have hh0 : (curvatureLiftPair f (0,0)).2 = 0 := by
    simp [curvatureLiftPair, asymmetricLift, curvatureNegativeProfile, C2, primitive]
  dsimp only at hg hh
  rw [hg0] at hg
  rw [hh0] at hh
  exact ⟨le_trans hzero hg, hh⟩

/-- A common constant offset retains the exact difference and makes both
streams nonnegative on nonnegative inputs, with no sign condition on `f 0`. -/
noncomputable def normalizedCurvatureLiftPair (f : ℝ → ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  ((curvatureLiftPair f z).1 + max (-f 0) 0,
   (curvatureLiftPair f z).2 + max (-f 0) 0)

theorem normalized_curvature_monotone_dc_split (f : ℝ → ℝ)
    (hf : Differentiable ℝ f)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)) :
    ConvexOn ℝ univ (fun z => (normalizedCurvatureLiftPair f z).1) ∧
    ConvexOn ℝ univ (fun z => (normalizedCurvatureLiftPair f z).2) ∧
    Monotone (fun z => (normalizedCurvatureLiftPair f z).1) ∧
    Monotone (fun z => (normalizedCurvatureLiftPair f z).2) ∧
    ValidPairActivation f (normalizedCurvatureLiftPair f) := by
  have hs := curvature_monotone_dc_split f hf hAC hq
  refine ⟨hs.1.add_const _, hs.2.1.add_const _, ?_, ?_, ?_⟩
  · intro a b hab
    exact add_le_add (hs.2.2.1 hab) le_rfl
  · intro a b hab
    exact add_le_add (hs.2.2.2.1 hab) le_rfl
  · intro a b
    have h := hs.2.2.2.2 a b
    dsimp [normalizedCurvatureLiftPair]
    linarith

theorem normalizedCurvatureLiftPair_nonnegative (f : ℝ → ℝ)
    (hf : Differentiable ℝ f)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)) :
    NonnegativePairActivation (normalizedCurvatureLiftPair f) := by
  intro a b ha hb
  have hs := normalized_curvature_monotone_dc_split f hf hAC hq
  have hg := hs.2.2.1 (show ((0,0) : ℝ × ℝ) ≤ (a,b) from ⟨ha,hb⟩)
  have hh := hs.2.2.2.1 (show ((0,0) : ℝ × ℝ) ≤ (a,b) from ⟨ha,hb⟩)
  have hg0 : (normalizedCurvatureLiftPair f (0,0)).1 = f 0 + max (-f 0) 0 := by
    simp [normalizedCurvatureLiftPair, curvatureLiftPair, asymmetricLift,
      curvaturePositiveProfile, C1, primitive]
  have hh0 : (normalizedCurvatureLiftPair f (0,0)).2 = max (-f 0) 0 := by
    simp [normalizedCurvatureLiftPair, curvatureLiftPair, asymmetricLift,
      curvatureNegativeProfile, C2, primitive]
  dsimp only at hg hh
  rw [hg0] at hg
  rw [hh0] at hh
  have hc : -f 0 ≤ max (-f 0) 0 := le_max_left _ _
  have hc0 : 0 ≤ max (-f 0) 0 := le_max_right _ _
  exact ⟨le_trans (by linarith) hg, le_trans hc0 hh⟩

/-- The slope at plus infinity: the slope at minus infinity plus the total
signed curvature. -/
noncomputable def plusInfinitySlope (f : ℝ → ℝ) : ℝ :=
  minusInfinitySlope f + ∫ t, curvature f t

/-- The derivative has a finite limit at plus infinity; no limit is assumed. -/
theorem derivative_limit_atTop (f : ℝ → ℝ)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)) :
    Tendsto (deriv f) atTop (𝓝 (plusInfinitySlope f)) := by
  have hc : Tendsto (cumulative (curvature f)) atTop (𝓝 (∫ t, curvature f t)) :=
    (aecover_Iic tendsto_id).integral_tendsto_of_countably_generated hq
  have hlim : Tendsto (fun x => minusInfinitySlope f + cumulative (curvature f) x) atTop
      (𝓝 (plusInfinitySlope f)) := tendsto_const_nhds.add hc
  exact hlim.congr' (Eventually.of_forall (fun x =>
    (derivative_cumulative_representation f hAC hq x).symm))

theorem total_curvature_signed (f : ℝ → ℝ) (hq : Integrable (curvature f)) :
    totalPositiveCurvature f - totalNegativeCurvature f = ∫ t, curvature f t := by
  unfold totalPositiveCurvature totalNegativeCurvature
  rw [← integral_sub (positiveCurvature_integrable f hq)
    (negativeCurvature_integrable f hq)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    dsimp only
    rw [positiveCurvature_eq_absolute, negativeCurvature_eq_absolute]
    ring)

theorem lift_width_arithmetic (s P N : ℝ) :
    max (s + max (-s) 0 + P) (max (-s) 0 + N) = (P + N + |s| + |s + (P - N)|) / 2 := by
  rcases le_total s 0 with hs | hs
  · rw [max_eq_left (neg_nonneg.mpr hs), abs_of_nonpos hs]
    rcases le_total (s + (P - N)) 0 with h | h
    · rw [abs_of_nonpos h, max_eq_right (by linarith)]
      ring
    · rw [abs_of_nonneg h, max_eq_left (by linarith)]
      ring
  · rw [max_eq_right (neg_nonpos.mpr hs), abs_of_nonneg hs]
    rcases le_total (s + (P - N)) 0 with h | h
    · rw [abs_of_nonpos h, max_eq_right (by linarith)]
      ring
    · rw [abs_of_nonneg h, max_eq_left (by linarith)]
      ring

/-- The common coefficient of the lift is the printed
`(‖f''‖₁ + |s₋| + |s₊|)/2`. -/
theorem curvatureLiftWidth_eq (f : ℝ → ℝ) (hq : Integrable (curvature f)) :
    curvatureLiftWidth f =
      ((∫ t, |curvature f t|) + |minusInfinitySlope f| + |plusInfinitySlope f|) / 2 := by
  unfold curvatureLiftWidth curvatureSlopeShift plusInfinitySlope
  rw [← total_curvature_eq_absolute f hq, ← total_curvature_signed f hq,
    lift_width_arithmetic]

/-- The primitive `D` of the thesis: `|f 0| + |s₋| z + ∫₀ᶻ V`, where `V` is the
cumulative absolute curvature. -/
noncomputable def absoluteCurvaturePrimitive (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  |f 0| + |minusInfinitySlope f| * x +
    ∫ t in (0 : ℝ)..x, cumulative (fun u => |curvature f u|) t

theorem cumulative_abs_split (f : ℝ → ℝ) (hq : Integrable (curvature f)) (x : ℝ) :
    cumulative (positiveCurvature f) x + cumulative (negativeCurvature f) x =
      cumulative (fun u => |curvature f u|) x := by
  unfold cumulative
  rw [← integral_add ((positiveCurvature_integrable f hq).integrableOn (s := Iic x))
    ((negativeCurvature_integrable f hq).integrableOn (s := Iic x))]
  congr 1
  funext t
  rw [positiveCurvature_eq_absolute, negativeCurvature_eq_absolute]
  ring

theorem absoluteCurvaturePrimitive_hasDerivAt (f : ℝ → ℝ)
    (hq : Integrable (curvature f)) (x : ℝ) :
    HasDerivAt (absoluteCurvaturePrimitive f)
      (|minusInfinitySlope f| + cumulative (fun u => |curvature f u|) x) x := by
  have h1 : HasDerivAt (fun y : ℝ => |f 0| + |minusInfinitySlope f| * y)
      (|minusInfinitySlope f|) x := by
    simpa using ((hasDerivAt_id x).const_mul |minusInfinitySlope f|).const_add |f 0|
  have h2 := ((cumulative_continuous _ hq.abs).integral_hasStrictDerivAt 0 x).hasDerivAt
  exact h1.fun_add h2

/-- The profiles of the normalized lift: the Jordan primitives with the common
linear shift and the common constant offset. -/
noncomputable def normalizedPositiveProfile (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  curvaturePositiveProfile f x + max (-f 0) 0

noncomputable def normalizedNegativeProfile (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  curvatureNegativeProfile f x + max (-f 0) 0

/-- The normalized profiles are the printed `p = (D+f)/2` and `q = (D-f)/2`. -/
theorem normalized_profiles_eq (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)) (x : ℝ) :
    normalizedPositiveProfile f x = (absoluteCurvaturePrimitive f x + f x) / 2 ∧
    normalizedNegativeProfile f x = (absoluteCurvaturePrimitive f x - f x) / 2 := by
  have hdiff := curvature_profile_difference f hf hAC hq x
  have hsum : curvaturePositiveProfile f x + curvatureNegativeProfile f x +
      2 * max (-f 0) 0 = absoluteCurvaturePrimitive f x := by
    have hd (y : ℝ) : HasDerivAt (fun z => curvaturePositiveProfile f z +
        curvatureNegativeProfile f z - absoluteCurvaturePrimitive f z) 0 y := by
      have h := ((curvaturePositiveProfile_hasDerivAt f hq y).fun_add
        (curvatureNegativeProfile_hasDerivAt f hq y)).fun_sub
        (absoluteCurvaturePrimitive_hasDerivAt f hq y)
      have hz : D1 f y + curvatureSlopeShift f + (D2 f y + curvatureSlopeShift f) -
          (|minusInfinitySlope f| + cumulative (fun u => |curvature f u|) y) = 0 := by
        rw [← cumulative_abs_split f hq y]
        have hs : minusInfinitySlope f + 2 * curvatureSlopeShift f =
            |minusInfinitySlope f| := by
          unfold curvatureSlopeShift
          rcases le_total (minusInfinitySlope f) 0 with h | h
          · rw [max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h]
            ring
          · rw [max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h]
            ring
        dsimp [D1, D2, slope]
        linarith
      rw [hz] at h
      exact h
    have heq := is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt)
      (fun y => (hd y).deriv) x 0
    have h0 : curvaturePositiveProfile f 0 + curvatureNegativeProfile f 0 -
        absoluteCurvaturePrimitive f 0 = f 0 - |f 0| := by
      simp [curvaturePositiveProfile, curvatureNegativeProfile,
        absoluteCurvaturePrimitive, C1, C2, primitive]
    have ha : f 0 + 2 * max (-f 0) 0 = |f 0| := by
      rcases le_total (f 0) 0 with h | h
      · rw [max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h]
        ring
      · rw [max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h]
        ring
    beta_reduce at heq
    linarith
  unfold normalizedPositiveProfile normalizedNegativeProfile
  constructor <;> linarith

theorem normalizedCurvatureLiftPair_eq_lift (f : ℝ → ℝ) (z : ℝ × ℝ) :
    normalizedCurvatureLiftPair f z =
      (asymmetricLift (normalizedPositiveProfile f) (curvatureLiftWidth f) z,
       asymmetricLift (normalizedNegativeProfile f) (curvatureLiftWidth f) z) := by
  apply Prod.ext <;>
    simp only [normalizedCurvatureLiftPair, curvatureLiftPair, asymmetricLift,
      normalizedPositiveProfile, normalizedNegativeProfile] <;> ring

/-- Thesis thm:absolute_curvature_split in full: both slope limits exist, the
coefficient is `(‖f''‖₁+|s₋|+|s₊|)/2`, the profiles are `(D±f)/2`, convex, with
slopes in `[0,L]` and the printed values at zero, and the resulting lift is a
convex, coordinatewise non-decreasing valid pair, non-negative on the
non-negative quadrant. -/
theorem absolute_curvature_split (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hAC : ∀ a b, AbsolutelyContinuousOnInterval (deriv f) a b)
    (hq : Integrable (curvature f)) :
    Tendsto (deriv f) atBot (𝓝 (minusInfinitySlope f)) ∧
    Tendsto (deriv f) atTop (𝓝 (plusInfinitySlope f)) ∧
    curvatureLiftWidth f =
      ((∫ t, |curvature f t|) + |minusInfinitySlope f| + |plusInfinitySlope f|) / 2 ∧
    (∀ x, normalizedPositiveProfile f x = (absoluteCurvaturePrimitive f x + f x) / 2 ∧
      normalizedNegativeProfile f x = (absoluteCurvaturePrimitive f x - f x) / 2) ∧
    ConvexOn ℝ univ (normalizedPositiveProfile f) ∧
    ConvexOn ℝ univ (normalizedNegativeProfile f) ∧
    (∀ x, normalizedPositiveProfile f x - normalizedNegativeProfile f x = f x) ∧
    (∀ x, HasDerivAt (normalizedPositiveProfile f) (D1 f x + curvatureSlopeShift f) x ∧
      0 ≤ D1 f x + curvatureSlopeShift f ∧
      D1 f x + curvatureSlopeShift f ≤ curvatureLiftWidth f) ∧
    (∀ x, HasDerivAt (normalizedNegativeProfile f) (D2 f x + curvatureSlopeShift f) x ∧
      0 ≤ D2 f x + curvatureSlopeShift f ∧
      D2 f x + curvatureSlopeShift f ≤ curvatureLiftWidth f) ∧
    normalizedPositiveProfile f 0 = max (f 0) 0 ∧
    normalizedNegativeProfile f 0 = max (-f 0) 0 ∧
    (∀ z, normalizedCurvatureLiftPair f z =
      (asymmetricLift (normalizedPositiveProfile f) (curvatureLiftWidth f) z,
       asymmetricLift (normalizedNegativeProfile f) (curvatureLiftWidth f) z)) ∧
    ConvexOn ℝ univ (fun z => (normalizedCurvatureLiftPair f z).1) ∧
    ConvexOn ℝ univ (fun z => (normalizedCurvatureLiftPair f z).2) ∧
    Monotone (fun z => (normalizedCurvatureLiftPair f z).1) ∧
    Monotone (fun z => (normalizedCurvatureLiftPair f z).2) ∧
    ValidPairActivation f (normalizedCurvatureLiftPair f) ∧
    NonnegativePairActivation (normalizedCurvatureLiftPair f) := by
  have hs := normalized_curvature_monotone_dc_split f hf hAC hq
  have hb := curvature_profile_slope_bounds f hq
  refine ⟨derivative_limit_atBot f hAC hq, derivative_limit_atTop f hAC hq,
    curvatureLiftWidth_eq f hq, normalized_profiles_eq f hf hAC hq,
    (curvaturePositiveProfile_convex f hq).add_const _,
    (curvatureNegativeProfile_convex f hq).add_const _, ?_, ?_, ?_, ?_, ?_,
    normalizedCurvatureLiftPair_eq_lift f, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1,
    hs.2.2.2.2, normalizedCurvatureLiftPair_nonnegative f hf hAC hq⟩
  · intro x
    have h := curvature_profile_difference f hf hAC hq x
    unfold normalizedPositiveProfile normalizedNegativeProfile
    linarith
  · intro x
    exact ⟨(curvaturePositiveProfile_hasDerivAt f hq x).add_const _, (hb x).1.1, (hb x).1.2⟩
  · intro x
    exact ⟨(curvatureNegativeProfile_hasDerivAt f hq x).add_const _, (hb x).2.1, (hb x).2.2⟩
  · have h : f 0 + max (-f 0) 0 = max (f 0) 0 := by
      rcases le_total (f 0) 0 with h | h
      · rw [max_eq_left (neg_nonneg.mpr h), max_eq_right h]
        ring
      · rw [max_eq_right (neg_nonpos.mpr h), max_eq_left h]
        ring
    simpa [normalizedPositiveProfile, curvaturePositiveProfile, C1, primitive] using h
  · simp [normalizedNegativeProfile, curvatureNegativeProfile, C2, primitive]

end HiddenMonotonicity.SmoothDC
