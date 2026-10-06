import PDE.ProductMeanPoincare

/-!
# Geometric mean Poincaré on the unit square and cube

The hypotheses are square integrability of the function and its actual line
derivatives, and absolute continuity on almost every coordinate line (ACL).
The constant `1` is derived from the unit side lengths by tensorization.
There is no trace or boundary condition on the function.

The actual distributional `H1` estimate is proved separately in `PDE.SobolevCube`
by direct weak-slice integration. A simultaneous pointwise ACL representative
is not needed for that estimate. The L⁶ Sobolev estimate remains separate.
-/

open MeasureTheory Set
open scoped ENNReal

namespace PDE

noncomputable def unitIntervalMeasure : Measure ℝ := volume.restrict (Icc 0 1)

instance unitIntervalMeasure_isProbabilityMeasure : IsProbabilityMeasure unitIntervalMeasure :=
  ⟨by simp [unitIntervalMeasure, Real.volume_Icc]⟩

noncomputable def unitSquareMeasure : Measure (ℝ × ℝ) :=
  unitIntervalMeasure.prod unitIntervalMeasure

instance unitSquareMeasure_isProbabilityMeasure : IsProbabilityMeasure unitSquareMeasure := by
  unfold unitSquareMeasure
  infer_instance

noncomputable def unitCubeMeasure : Measure (ℝ × (ℝ × ℝ)) :=
  unitIntervalMeasure.prod unitSquareMeasure

instance unitCubeMeasure_isProbabilityMeasure : IsProbabilityMeasure unitCubeMeasure := by
  unfold unitCubeMeasure
  infer_instance

/-- The product probability measure is ordinary Lebesgue measure on the square. -/
theorem unitSquareMeasure_eq_volume_restrict :
    unitSquareMeasure = volume.restrict ((Icc (0 : ℝ) 1) ×ˢ (Icc (0 : ℝ) 1)) := by
  rw [unitSquareMeasure, unitIntervalMeasure, Measure.prod_restrict, ← Measure.volume_eq_prod]

/-- The cube theorem uses ordinary, unweighted three-dimensional volume. -/
theorem unitCubeMeasure_eq_volume_restrict :
    unitCubeMeasure = volume.restrict
      ((Icc (0 : ℝ) 1) ×ˢ ((Icc (0 : ℝ) 1) ×ˢ (Icc (0 : ℝ) 1))) := by
  rw [unitCubeMeasure, unitSquareMeasure_eq_volume_restrict, unitIntervalMeasure,
    Measure.prod_restrict, ← Measure.volume_eq_prod]

private theorem slice_interval_energy {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod unitIntervalMeasure))
    (hd : MemLp (fun z => deriv (fun t => f (z.1, t)) z.2) 2 (μ.prod unitIntervalMeasure))
    (hac : ∀ᵐ x ∂μ, AbsolutelyContinuousOnInterval (fun t => f (x, t)) 0 1) :
    (∫ z, (f z - ∫ y, f (z.1, y) ∂unitIntervalMeasure) ^ 2 ∂μ.prod unitIntervalMeasure) ≤
      ∫ z, deriv (fun t => f (z.1, t)) z.2 ^ 2 ∂μ.prod unitIntervalMeasure := by
  have hosc : Integrable
      (fun z => (f z - ∫ y, f (z.1, y) ∂unitIntervalMeasure) ^ 2) (μ.prod unitIntervalMeasure) :=
    (hf.sub ((memLp_two_integral_right hf).comp_fst unitIntervalMeasure)).integrable_sq
  rw [integral_prod _ hosc, integral_prod _ hd.integrable_sq]
  apply integral_mono_ae hosc.integral_prod_left hd.integrable_sq.integral_prod_left
  filter_upwards [hac, memLp_two_slice_right_ae hd] with x hx hdx
  simpa only [sub_zero, div_one, one_pow, one_mul, unitIntervalMeasure] using
    interval_mean_poincare (by norm_num : (0 : ℝ) < 1) hx hdx

/-- A unit square has mean Poincaré constant at most one for ACL functions
with square-integrable line derivatives. Endpoint values are unrestricted. -/
theorem unitSquare_mean_poincare {f : ℝ × ℝ → ℝ}
    (hf : MemLp f 2 unitSquareMeasure)
    (hdx : MemLp (fun z => deriv (fun t => f (t, z.2)) z.1) 2 unitSquareMeasure)
    (hdy : MemLp (fun z => deriv (fun t => f (z.1, t)) z.2) 2 unitSquareMeasure)
    (hacx : ∀ᵐ y ∂unitIntervalMeasure, AbsolutelyContinuousOnInterval (fun t => f (t, y)) 0 1)
    (hacy : ∀ᵐ x ∂unitIntervalMeasure, AbsolutelyContinuousOnInterval (fun t => f (x, t)) 0 1) :
    (∫ z, (f z - ∫ w, f w ∂unitSquareMeasure) ^ 2 ∂unitSquareMeasure) ≤
      ∫ z, (deriv (fun t => f (t, z.2)) z.1) ^ 2 +
        (deriv (fun t => f (z.1, t)) z.2) ^ 2 ∂unitSquareMeasure := by
  have hswap : MemLp (fun z : ℝ × ℝ => f z.swap) 2 unitSquareMeasure :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable.prod_swap).mpr hf.integrable_sq.swap
  have hdswap : MemLp (fun z : ℝ × ℝ => deriv (fun t => f (t, z.1)) z.2) 2 unitSquareMeasure :=
    (memLp_two_iff_integrable_sq hdx.aestronglyMeasurable.prod_swap).mpr hdx.integrable_sq.swap
  have hy := slice_interval_energy hf hdy hacy
  have hx := slice_interval_energy hswap hdswap hacx
  have hx' : (∫ z, (f z - ∫ x, f (x, z.2) ∂unitIntervalMeasure) ^ 2 ∂unitSquareMeasure) ≤
      ∫ z, deriv (fun t => f (t, z.2)) z.1 ^ 2 ∂unitSquareMeasure := by
    calc
      _ = ∫ z, (f z.swap - ∫ x, f (x, z.1) ∂unitIntervalMeasure) ^ 2
          ∂unitIntervalMeasure.prod unitIntervalMeasure :=
        (integral_prod_swap (fun z => (f z - ∫ x, f (x, z.2) ∂unitIntervalMeasure) ^ 2)).symm
      _ ≤ _ := hx
      _ = _ := integral_prod_swap (fun z => deriv (fun t => f (t, z.2)) z.1 ^ 2)
  have ht := integral_sq_sub_mean_prod_le hf
  change (∫ z, (f z - ∫ w, f w ∂unitSquareMeasure) ^ 2 ∂unitSquareMeasure) ≤ _ at ht
  calc
    _ ≤ _ := ht.trans (add_le_add hy hx')
    _ = _ := by
      rw [integral_add hdx.integrable_sq hdy.integrable_sq]
      simp only [unitSquareMeasure]
      ring

/-- A genuine three-dimensional mean Poincaré estimate on the unit cube.
The right side consists of the three actual line derivative energies, and
the geometric constant is one. No Poincaré inequality is assumed. -/
theorem unitCube_mean_poincare {f : ℝ × (ℝ × ℝ) → ℝ}
    (hf : MemLp f 2 unitCubeMeasure)
    (hdx : MemLp (fun z => deriv (fun t => f (t, z.2)) z.1) 2 unitCubeMeasure)
    (hdy : MemLp (fun z => deriv (fun t => f (z.1, t, z.2.2)) z.2.1) 2 unitCubeMeasure)
    (hdz : MemLp (fun z => deriv (fun t => f (z.1, z.2.1, t)) z.2.2) 2 unitCubeMeasure)
    (hacx : ∀ᵐ y ∂unitSquareMeasure,
      AbsolutelyContinuousOnInterval (fun t => f (t, y)) 0 1)
    (hacy : ∀ᵐ x ∂unitIntervalMeasure, ∀ᵐ z ∂unitIntervalMeasure,
      AbsolutelyContinuousOnInterval (fun t => f (x, t, z)) 0 1)
    (hacz : ∀ᵐ x ∂unitIntervalMeasure, ∀ᵐ y ∂unitIntervalMeasure,
      AbsolutelyContinuousOnInterval (fun t => f (x, y, t)) 0 1) :
    (∫ z, (f z - ∫ w, f w ∂unitCubeMeasure) ^ 2 ∂unitCubeMeasure) ≤
      ∫ z, (deriv (fun t => f (t, z.2)) z.1) ^ 2 +
        (deriv (fun t => f (z.1, t, z.2.2)) z.2.1) ^ 2 +
        (deriv (fun t => f (z.1, z.2.1, t)) z.2.2) ^ 2 ∂unitCubeMeasure := by
  have hosc : Integrable
      (fun z => (f z - ∫ y, f (z.1, y) ∂unitSquareMeasure) ^ 2) unitCubeMeasure :=
    (hf.sub ((memLp_two_integral_right hf).comp_fst unitSquareMeasure)).integrable_sq
  have hiyz : Integrable (fun z =>
      (deriv (fun t => f (z.1, t, z.2.2)) z.2.1) ^ 2 +
        (deriv (fun t => f (z.1, z.2.1, t)) z.2.2) ^ 2) unitCubeMeasure :=
    hdy.integrable_sq.add hdz.integrable_sq
  have hyz : (∫ z, (f z - ∫ y, f (z.1, y) ∂unitSquareMeasure) ^ 2 ∂unitCubeMeasure) ≤
      ∫ z, (deriv (fun t => f (z.1, t, z.2.2)) z.2.1) ^ 2 +
        (deriv (fun t => f (z.1, z.2.1, t)) z.2.2) ^ 2 ∂unitCubeMeasure := by
    unfold unitCubeMeasure
    rw [integral_prod _ hosc, integral_prod _ hiyz]
    apply integral_mono_ae hosc.integral_prod_left hiyz.integral_prod_left
    filter_upwards [memLp_two_slice_right_ae hf, memLp_two_slice_right_ae hdy,
      memLp_two_slice_right_ae hdz, hacy, hacz] with x hfx hdyx hdzx hacyx haczx
    exact unitSquare_mean_poincare hfx hdyx hdzx hacyx haczx
  have hswap : MemLp (fun z : (ℝ × ℝ) × ℝ => f z.swap) 2
      (unitSquareMeasure.prod unitIntervalMeasure) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable.prod_swap).mpr hf.integrable_sq.swap
  have hdswap : MemLp (fun z : (ℝ × ℝ) × ℝ => deriv (fun t => f (t, z.1)) z.2) 2
      (unitSquareMeasure.prod unitIntervalMeasure) :=
    (memLp_two_iff_integrable_sq hdx.aestronglyMeasurable.prod_swap).mpr hdx.integrable_sq.swap
  have hx := slice_interval_energy hswap hdswap hacx
  have hx' : (∫ z, (f z - ∫ x, f (x, z.2) ∂unitIntervalMeasure) ^ 2 ∂unitCubeMeasure) ≤
      ∫ z, deriv (fun t => f (t, z.2)) z.1 ^ 2 ∂unitCubeMeasure := by
    calc
      _ = ∫ z, (f z.swap - ∫ x, f (x, z.1) ∂unitIntervalMeasure) ^ 2
          ∂unitSquareMeasure.prod unitIntervalMeasure :=
        (integral_prod_swap (fun z => (f z - ∫ x, f (x, z.2) ∂unitIntervalMeasure) ^ 2)).symm
      _ ≤ _ := hx
      _ = _ := integral_prod_swap (fun z => deriv (fun t => f (t, z.2)) z.1 ^ 2)
  have ht := integral_sq_sub_mean_prod_le hf
  change (∫ z, (f z - ∫ w, f w ∂unitCubeMeasure) ^ 2 ∂unitCubeMeasure) ≤ _ at ht
  calc
    _ ≤ _ := ht.trans (add_le_add hyz hx')
    _ = _ := by
      have hixy : Integrable (fun z =>
          (deriv (fun t => f (t, z.2)) z.1) ^ 2 +
            (deriv (fun t => f (z.1, t, z.2.2)) z.2.1) ^ 2) unitCubeMeasure :=
        hdx.integrable_sq.add hdy.integrable_sq
      rw [integral_add hdy.integrable_sq hdz.integrable_sq,
        integral_add hixy hdz.integrable_sq,
        integral_add hdx.integrable_sq hdy.integrable_sq]
      ring

/-- The same geometric cube estimate in the real L² norm used by the
positive-mass temperature bounds. -/
theorem unitCube_mean_poincare_lpNorm {f : ℝ × (ℝ × ℝ) → ℝ}
    (hf : MemLp f 2 unitCubeMeasure)
    (hdx : MemLp (fun z => deriv (fun t => f (t, z.2)) z.1) 2 unitCubeMeasure)
    (hdy : MemLp (fun z => deriv (fun t => f (z.1, t, z.2.2)) z.2.1) 2 unitCubeMeasure)
    (hdz : MemLp (fun z => deriv (fun t => f (z.1, z.2.1, t)) z.2.2) 2 unitCubeMeasure)
    (hacx : ∀ᵐ y ∂unitSquareMeasure,
      AbsolutelyContinuousOnInterval (fun t => f (t, y)) 0 1)
    (hacy : ∀ᵐ x ∂unitIntervalMeasure, ∀ᵐ z ∂unitIntervalMeasure,
      AbsolutelyContinuousOnInterval (fun t => f (x, t, z)) 0 1)
    (hacz : ∀ᵐ x ∂unitIntervalMeasure, ∀ᵐ y ∂unitIntervalMeasure,
      AbsolutelyContinuousOnInterval (fun t => f (x, y, t)) 0 1) :
    lpNorm (fun z => f z - ∫ w, f w ∂unitCubeMeasure) 2 unitCubeMeasure ≤
      Real.sqrt (∫ z, (deriv (fun t => f (t, z.2)) z.1) ^ 2 +
        (deriv (fun t => f (z.1, t, z.2.2)) z.2.1) ^ 2 +
        (deriv (fun t => f (z.1, z.2.1, t)) z.2.2) ^ 2 ∂unitCubeMeasure) := by
  have hosc : MemLp (fun z => f z - ∫ w, f w ∂unitCubeMeasure) 2 unitCubeMeasure :=
    hf.sub (memLp_const _)
  rw [lpNorm_two_eq_sqrt_integral_sq hosc]
  exact Real.sqrt_le_sqrt (unitCube_mean_poincare hf hdx hdy hdz hacx hacy hacz)

end PDE
