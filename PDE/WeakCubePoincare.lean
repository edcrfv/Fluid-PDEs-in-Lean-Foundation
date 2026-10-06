import PDE.CubePoincare
import PDE.DistributionalInterval

/-! Geometric mean Poincaré using weak slices directly. This avoids choosing
one globally ACL pointwise representative from independent line representatives. -/

open MeasureTheory Set
open scoped ENNReal

namespace PDE

private theorem slice_weak_interval_energy {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {f df : α × ℝ → ℝ}
    (hf : MemLp f 2 (μ.prod unitIntervalMeasure))
    (hd : MemLp df 2 (μ.prod unitIntervalMeasure))
    (hweak : ∀ᵐ x ∂μ, HasWeakDerivativeOnInterval 0 1 (fun t => f (x, t)) (fun t => df (x, t))) :
    (∫ z, (f z - ∫ y, f (z.1, y) ∂unitIntervalMeasure) ^ 2 ∂μ.prod unitIntervalMeasure) ≤
      ∫ z, df z ^ 2 ∂μ.prod unitIntervalMeasure := by
  have hosc : Integrable
      (fun z => (f z - ∫ y, f (z.1, y) ∂unitIntervalMeasure) ^ 2) (μ.prod unitIntervalMeasure) :=
    (hf.sub ((memLp_two_integral_right hf).comp_fst unitIntervalMeasure)).integrable_sq
  rw [integral_prod _ hosc, integral_prod _ hd.integrable_sq]
  apply integral_mono_ae hosc.integral_prod_left hd.integrable_sq.integral_prod_left
  filter_upwards [hweak, memLp_two_slice_right_ae hf, memLp_two_slice_right_ae hd] with x hx hfx hdx
  simpa only [sub_zero, div_one, one_pow, one_mul, unitIntervalMeasure] using
    hx.mean_poincare (by norm_num : (0 : ℝ) < 1) hfx hdx

/-- Mean Poincaré on a square from distributional weak line derivatives.
No pointwise ACL representative or boundary condition is supplied. -/
theorem unitSquare_mean_poincare_of_weak_slices {f dx dy : ℝ × ℝ → ℝ}
    (hf : MemLp f 2 unitSquareMeasure)
    (hdx : MemLp dx 2 unitSquareMeasure)
    (hdy : MemLp dy 2 unitSquareMeasure)
    (hweakx : ∀ᵐ y ∂unitIntervalMeasure, HasWeakDerivativeOnInterval 0 1 (fun t => f (t, y)) (fun t => dx (t, y)))
    (hweaky : ∀ᵐ x ∂unitIntervalMeasure, HasWeakDerivativeOnInterval 0 1 (fun t => f (x, t)) (fun t => dy (x, t))) :
    (∫ z, (f z - ∫ w, f w ∂unitSquareMeasure) ^ 2 ∂unitSquareMeasure) ≤
      ∫ z, (dx z) ^ 2 +
        (dy z) ^ 2 ∂unitSquareMeasure := by
  have hswap : MemLp (fun z : ℝ × ℝ => f z.swap) 2 unitSquareMeasure :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable.prod_swap).mpr hf.integrable_sq.swap
  have hdswap : MemLp (fun z : ℝ × ℝ => dx z.swap) 2 unitSquareMeasure :=
    (memLp_two_iff_integrable_sq hdx.aestronglyMeasurable.prod_swap).mpr hdx.integrable_sq.swap
  have hy := slice_weak_interval_energy hf hdy hweaky
  have hx := slice_weak_interval_energy hswap hdswap hweakx
  have hx' : (∫ z, (f z - ∫ x, f (x, z.2) ∂unitIntervalMeasure) ^ 2 ∂unitSquareMeasure) ≤
      ∫ z, dx z ^ 2 ∂unitSquareMeasure := by
    calc
      _ = ∫ z, (f z.swap - ∫ x, f (x, z.1) ∂unitIntervalMeasure) ^ 2
          ∂unitIntervalMeasure.prod unitIntervalMeasure :=
        (integral_prod_swap (fun z => (f z - ∫ x, f (x, z.2) ∂unitIntervalMeasure) ^ 2)).symm
      _ ≤ _ := hx
      _ = _ := integral_prod_swap (fun z => dx z ^ 2)
  have ht := integral_sq_sub_mean_prod_le hf
  change (∫ z, (f z - ∫ w, f w ∂unitSquareMeasure) ^ 2 ∂unitSquareMeasure) ≤ _ at ht
  calc
    _ ≤ _ := ht.trans (add_le_add hy hx')
    _ = _ := by
      rw [integral_add hdx.integrable_sq hdy.integrable_sq]
      simp only [unitSquareMeasure]
      ring

/-- Three-dimensional mean Poincaré from a.e. weak slices in each direction.
The fields are tied to their slices by actual compact-test weak identities. -/
theorem unitCube_mean_poincare_of_weak_slices {f dx dy dz : ℝ × (ℝ × ℝ) → ℝ}
    (hf : MemLp f 2 unitCubeMeasure)
    (hdx : MemLp dx 2 unitCubeMeasure)
    (hdy : MemLp dy 2 unitCubeMeasure)
    (hdz : MemLp dz 2 unitCubeMeasure)
    (hweakx : ∀ᵐ y ∂unitSquareMeasure,
      HasWeakDerivativeOnInterval 0 1 (fun t => f (t, y)) (fun t => dx (t, y)))
    (hweaky : ∀ᵐ x ∂unitIntervalMeasure, ∀ᵐ z ∂unitIntervalMeasure,
      HasWeakDerivativeOnInterval 0 1 (fun t => f (x, t, z)) (fun t => dy (x, t, z)))
    (hweakz : ∀ᵐ x ∂unitIntervalMeasure, ∀ᵐ y ∂unitIntervalMeasure,
      HasWeakDerivativeOnInterval 0 1 (fun t => f (x, y, t)) (fun t => dz (x, y, t))) :
    (∫ z, (f z - ∫ w, f w ∂unitCubeMeasure) ^ 2 ∂unitCubeMeasure) ≤
      ∫ z, (dx z) ^ 2 +
        (dy z) ^ 2 +
        (dz z) ^ 2 ∂unitCubeMeasure := by
  have hosc : Integrable
      (fun z => (f z - ∫ y, f (z.1, y) ∂unitSquareMeasure) ^ 2) unitCubeMeasure :=
    (hf.sub ((memLp_two_integral_right hf).comp_fst unitSquareMeasure)).integrable_sq
  have hiyz : Integrable (fun z =>
      (dy z) ^ 2 +
        (dz z) ^ 2) unitCubeMeasure :=
    hdy.integrable_sq.add hdz.integrable_sq
  have hyz : (∫ z, (f z - ∫ y, f (z.1, y) ∂unitSquareMeasure) ^ 2 ∂unitCubeMeasure) ≤
      ∫ z, (dy z) ^ 2 +
        (dz z) ^ 2 ∂unitCubeMeasure := by
    unfold unitCubeMeasure
    rw [integral_prod _ hosc, integral_prod _ hiyz]
    apply integral_mono_ae hosc.integral_prod_left hiyz.integral_prod_left
    filter_upwards [memLp_two_slice_right_ae hf, memLp_two_slice_right_ae hdy,
      memLp_two_slice_right_ae hdz, hweaky, hweakz] with x hfx hdyx hdzx hweakyx hweakzx
    exact unitSquare_mean_poincare_of_weak_slices hfx hdyx hdzx hweakyx hweakzx
  have hswap : MemLp (fun z : (ℝ × ℝ) × ℝ => f z.swap) 2
      (unitSquareMeasure.prod unitIntervalMeasure) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable.prod_swap).mpr hf.integrable_sq.swap
  have hdswap : MemLp (fun z : (ℝ × ℝ) × ℝ => dx z.swap) 2
      (unitSquareMeasure.prod unitIntervalMeasure) :=
    (memLp_two_iff_integrable_sq hdx.aestronglyMeasurable.prod_swap).mpr hdx.integrable_sq.swap
  have hx := slice_weak_interval_energy hswap hdswap hweakx
  have hx' : (∫ z, (f z - ∫ x, f (x, z.2) ∂unitIntervalMeasure) ^ 2 ∂unitCubeMeasure) ≤
      ∫ z, dx z ^ 2 ∂unitCubeMeasure := by
    calc
      _ = ∫ z, (f z.swap - ∫ x, f (x, z.1) ∂unitIntervalMeasure) ^ 2
          ∂unitSquareMeasure.prod unitIntervalMeasure :=
        (integral_prod_swap (fun z => (f z - ∫ x, f (x, z.2) ∂unitIntervalMeasure) ^ 2)).symm
      _ ≤ _ := hx
      _ = _ := integral_prod_swap (fun z => dx z ^ 2)
  have ht := integral_sq_sub_mean_prod_le hf
  change (∫ z, (f z - ∫ w, f w ∂unitCubeMeasure) ^ 2 ∂unitCubeMeasure) ≤ _ at ht
  calc
    _ ≤ _ := ht.trans (add_le_add hyz hx')
    _ = _ := by
      have hixy : Integrable (fun z =>
          (dx z) ^ 2 +
            (dy z) ^ 2) unitCubeMeasure :=
        hdx.integrable_sq.add hdy.integrable_sq
      rw [integral_add hdy.integrable_sq hdz.integrable_sq,
        integral_add hixy hdz.integrable_sq,
        integral_add hdx.integrable_sq hdy.integrable_sq]
      ring

end PDE
