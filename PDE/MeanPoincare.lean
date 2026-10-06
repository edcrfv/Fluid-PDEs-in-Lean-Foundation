import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Mean Poincaré on an interval

The constant is derived from the length of the interval and the fundamental
theorem for absolutely continuous functions. No boundary value is prescribed.
This is a geometric building block, not yet a theorem about the distributional
Sobolev space on a general higher-dimensional domain.
-/

open MeasureTheory Set
open scoped ENNReal

namespace PDE

/-- The real L² norm is the square root of the actual square integral. -/
theorem lpNorm_two_eq_sqrt_integral_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : MemLp f 2 μ) :
    lpNorm f 2 μ = Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  norm_num [Real.sqrt_eq_rpow, Real.rpow_two, Real.norm_eq_abs]

/-- Expanding the square under a finite measure. -/
theorem integral_sq_sub_const {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : MemLp f 2 μ) (c : ℝ) :
    (∫ x, (f x - c) ^ 2 ∂μ) =
      (∫ x, f x ^ 2 ∂μ) - 2 * c * (∫ x, f x ∂μ) + μ.real univ * c ^ 2 := by
  have hi := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  calc
    _ = ∫ x, f x ^ 2 - (2 * c) * f x + c ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring
    _ = _ := by
      rw [integral_add
          (show Integrable (fun x => f x ^ 2 - (2 * c) * f x) μ from
            hf.integrable_sq.sub (hi.const_mul _)) (integrable_const _),
        integral_sub hf.integrable_sq (hi.const_mul _), integral_const_mul,
        integral_const, smul_eq_mul]

/-- The mean minimizes the squared distance to constants; no probability
normalization and no nonzero boundary condition is hidden in this statement. -/
theorem integral_sq_sub_mean_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : MemLp f 2 μ) (hμ : 0 < μ.real univ) (c : ℝ) :
    (∫ x, (f x - (∫ y, f y ∂μ) / μ.real univ) ^ 2 ∂μ) ≤
      ∫ x, (f x - c) ^ 2 ∂μ := by
  rw [integral_sq_sub_const hf, integral_sq_sub_const hf]
  have hm : μ.real univ * ((∫ y, f y ∂μ) / μ.real univ) = ∫ y, f y ∂μ :=
    mul_div_cancel₀ _ hμ.ne'
  have hm' := congrArg (fun z => (2 * c - 2 * ((∫ y, f y ∂μ) / μ.real univ)) * z) hm
  nlinarith [mul_nonneg hμ.le (sq_nonneg (c - (∫ y, f y ∂μ) / μ.real univ))]

/-- Cauchy–Schwarz for the integral of the absolute value, in square-root form. -/
theorem integral_abs_le_sqrt_measure_mul_sqrt_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, |f x| ∂μ) ≤ Real.sqrt (μ.real univ) * Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
    (f := fun _ => (1 : ℝ)) (g := f)
    (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : α => (1 : ℝ)) 2 μ))
    (by simpa using hf)
  simpa [Real.sqrt_eq_rpow, Real.rpow_two, Real.norm_eq_abs] using h

/-- An absolutely continuous function with square-integrable derivative has
uniform oscillation controlled by the interval length and the actual derivative. -/
theorem abs_sub_left_le_sqrt_interval_energy {f : ℝ → ℝ} {a b x : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b))) (hx : x ∈ Icc a b) :
    |f x - f a| ≤ Real.sqrt (b - a) * Real.sqrt (∫ y in Icc a b, deriv f y ^ 2) := by
  have hax : AbsolutelyContinuousOnInterval f a x := hf.mono (by
    simpa only [uIcc_of_le hab, uIcc_of_le hx.1] using Icc_subset_Icc le_rfl hx.2)
  have hfull : IntegrableOn (fun y => |deriv f y|) (Icc a b) :=
    (hd.integrable (by norm_num)).abs
  calc
    |f x - f a| = |∫ y in Icc a x, deriv f y| := by
      rw [← hax.integral_deriv_eq_sub, intervalIntegral.integral_of_le hx.1,
        integral_Icc_eq_integral_Ioc]
    _ ≤ ∫ y in Icc a x, |deriv f y| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (f := deriv f) (μ := volume.restrict (Icc a x)))
    _ ≤ ∫ y in Icc a b, |deriv f y| :=
      setIntegral_mono_set hfull (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        (Filter.Eventually.of_forall fun _ hy => Icc_subset_Icc le_rfl hx.2 hy)
    _ ≤ _ := by
      simpa [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using
        integral_abs_le_sqrt_measure_mul_sqrt_sq hd

/-- A mean Poincaré estimate with explicit geometric constant `(b-a)^2`.
The function may have arbitrary and unequal endpoint values. -/
theorem interval_mean_poincare {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b))) :
    (∫ x in Icc a b, (f x - (∫ y in Icc a b, f y) / (b - a)) ^ 2) ≤
      (b - a) ^ 2 * ∫ x in Icc a b, deriv f x ^ 2 := by
  have hc : ContinuousOn f (Icc a b) := by simpa [uIcc_of_le hab.le] using hf.continuousOn
  have hL2 : MemLp f 2 (volume.restrict (Icc a b)) :=
    (memLp_two_iff_integrable_sq hc.integrableOn_Icc.aestronglyMeasurable).mpr
      (hc.pow 2).integrableOn_Icc
  have hvol : (volume.restrict (Icc a b)).real univ = b - a := by
    simp [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  have he : 0 ≤ ∫ x in Icc a b, deriv f x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hpoint : ∀ᵐ x ∂volume.restrict (Icc a b),
      (f x - f a) ^ 2 ≤ (b - a) * ∫ y in Icc a b, deriv f y ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have h := abs_sub_left_le_sqrt_interval_energy hab.le hf hd hx
    have hs := mul_self_le_mul_self (abs_nonneg (f x - f a)) h
    simpa only [← sq, sq_abs, mul_pow, Real.sq_sqrt (sub_nonneg.mpr hab.le),
      Real.sq_sqrt he] using hs
  calc
    _ ≤ ∫ x in Icc a b, (f x - f a) ^ 2 := by
      simpa only [hvol] using integral_sq_sub_mean_le hL2 (hvol.symm ▸ sub_pos.mpr hab) (f a)
    _ ≤ ∫ _x in Icc a b, (b - a) * ∫ y in Icc a b, deriv f y ^ 2 :=
      integral_mono_ae (hL2.sub (memLp_const (f a))).integrable_sq (integrable_const _) hpoint
    _ = _ := by rw [integral_const, smul_eq_mul, hvol]; ring

end PDE
