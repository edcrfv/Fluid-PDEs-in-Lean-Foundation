import PDE.MeanPoincare
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Tensorization of mean oscillation

Under product probability measures, the full mean-square oscillation is at most
the sum of the mean-square oscillations in the two factors. Integrability of
the slice means is proved, not assumed. This supplies the product step for
geometric Poincaré estimates on cubes.
-/

open MeasureTheory Set
open scoped ENNReal

namespace PDE

/-- The square of a mean is at most the mean of the square. -/
theorem sq_integral_le_integral_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  have h : 0 ≤ ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg (f x - ∫ y, f y ∂μ)
  rw [integral_sq_sub_const hf] at h
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_mul] at h
  nlinarith

/-- Almost every slice of a square-integrable function is square integrable. -/
theorem memLp_two_slice_right_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y => f (x, y)) 2 ν := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left, hf.integrable_sq.prod_right_ae]
    with x hxm hxi
  exact (memLp_two_iff_integrable_sq hxm).mpr hxi

/-- Taking the mean in a probability factor preserves square integrability. -/
theorem memLp_two_integral_right {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [IsProbabilityMeasure ν]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun x => ∫ y, f (x, y) ∂ν) 2 μ := by
  have hm := hf.aestronglyMeasurable.integral_prod_right'
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply hf.integrable_sq.integral_prod_left.mono' (hm.pow 2)
  filter_upwards [memLp_two_slice_right_ae hf] with x hx
  change ‖(∫ y, f (x, y) ∂ν) ^ 2‖ ≤ _
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (∫ y, f (x, y) ∂ν))] using
    sq_integral_le_integral_sq hx

/-- Fubini and Cauchy–Schwarz give contraction of square energy under averaging. -/
theorem integral_sq_integral_right_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [IsProbabilityMeasure ν]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    (∫ x, (∫ y, f (x, y) ∂ν) ^ 2 ∂μ) ≤ ∫ z, f z ^ 2 ∂μ.prod ν := by
  rw [integral_prod _ hf.integrable_sq]
  exact integral_mono_ae (memLp_two_integral_right hf).integrable_sq
    hf.integrable_sq.integral_prod_left
    ((memLp_two_slice_right_ae hf).mono fun _ hx => sq_integral_le_integral_sq hx)

/-- Decomposition into oscillation in the second factor and oscillation of its mean. -/
theorem integral_sq_sub_mean_prod_eq {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    (∫ z, (f z - ∫ w, f w ∂μ.prod ν) ^ 2 ∂μ.prod ν) =
      (∫ z, (f z - ∫ y, f (z.1, y) ∂ν) ^ 2 ∂μ.prod ν) +
      ∫ x, ((∫ y, f (x, y) ∂ν) - ∫ w, f w ∂μ.prod ν) ^ 2 ∂μ := by
  let g := fun x => ∫ y, f (x, y) ∂ν
  have hg : MemLp g 2 μ := memLp_two_integral_right hf
  have hi := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hfg : MemLp (fun z => f z - g z.1) 2 (μ.prod ν) := hf.sub (hg.comp_fst ν)
  have hcenter : (∫ z, (f z - g z.1) ^ 2 ∂μ.prod ν) =
      (∫ z, f z ^ 2 ∂μ.prod ν) - ∫ x, g x ^ 2 ∂μ := by
    rw [integral_prod _ hfg.integrable_sq, integral_prod _ hf.integrable_sq,
      ← integral_sub hf.integrable_sq.integral_prod_left hg.integrable_sq]
    apply integral_congr_ae
    filter_upwards [memLp_two_slice_right_ae hf] with x hx
    rw [integral_sq_sub_const hx]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_mul]
    dsimp [g]
    ring
  change _ = (∫ z, (f z - g z.1) ^ 2 ∂μ.prod ν) +
    ∫ x, (g x - ∫ w, f w ∂μ.prod ν) ^ 2 ∂μ
  rw [hcenter, integral_sq_sub_const hf, integral_sq_sub_const hg]
  have hgint : (∫ x, g x ∂μ) = ∫ z, f z ∂μ.prod ν := (integral_prod _ hi).symm
  rw [hgint]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_mul]
  ring

/-- Mean oscillation tensorizes. Neither slice Poincaré estimates nor any
differentiability assumption is needed for this measure-theoretic step. -/
theorem integral_sq_sub_mean_prod_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    (∫ z, (f z - ∫ w, f w ∂μ.prod ν) ^ 2 ∂μ.prod ν) ≤
      (∫ z, (f z - ∫ y, f (z.1, y) ∂ν) ^ 2 ∂μ.prod ν) +
      ∫ z, (f z - ∫ x, f (x, z.2) ∂μ) ^ 2 ∂μ.prod ν := by
  rw [integral_sq_sub_mean_prod_eq hf]
  apply add_le_add le_rfl
  let h := fun y => ∫ x, f (x, y) ∂μ
  have hswap : MemLp (fun z : β × α => f z.swap) 2 (ν.prod μ) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable.prod_swap).mpr hf.integrable_sq.swap
  have hh : MemLp h 2 ν := memLp_two_integral_right hswap
  have hr : MemLp (fun z => f z - h z.2) 2 (μ.prod ν) := hf.sub (hh.comp_snd μ)
  have hc := integral_sq_integral_right_le hr
  have hi := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hhint : (∫ y, h y ∂ν) = ∫ z, f z ∂μ.prod ν := (integral_prod_symm _ hi).symm
  have hmeans : ∀ᵐ x ∂μ, (∫ y, f (x, y) - h y ∂ν) =
      (∫ y, f (x, y) ∂ν) - ∫ z, f z ∂μ.prod ν := by
    filter_upwards [hi.prod_right_ae] with x hx
    rw [integral_sub hx (hh.integrable (by norm_num)), hhint]
  have heq := integral_congr_ae (hmeans.mono fun _ hx => congrArg (fun z : ℝ => z ^ 2) hx)
  rwa [heq] at hc

end PDE
