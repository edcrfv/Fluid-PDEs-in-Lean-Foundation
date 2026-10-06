import PDE.WeightedEnergy
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Matching the extended-valued mixed estimate with real L6 norms. -/

open MeasureTheory
open scoped ENNReal

namespace PDE

theorem lintegral_ofReal_sq_eq_lpNorm_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) :
    (∫⁻ x, ENNReal.ofReal (f x) ^ 2 ∂μ) = ENNReal.ofReal (lpNorm f 2 μ ^ 2) := by
  rw [ENNReal.ofReal_pow lpNorm_nonneg, ofReal_lpNorm hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num only [show (2 : ℝ)⁻¹ * 2 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_two]
  apply lintegral_congr_ae
  filter_upwards [hf0] with x hx
  rw [Real.enorm_of_nonneg hx]

theorem lintegral_ofReal_six_rpow_eq_lpNorm_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 6 μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) :
    (∫⁻ x, (ENNReal.ofReal (f x)) ^ (6 : ℝ) ∂μ) ^ (1 / 3 : ℝ) =
      ENNReal.ofReal (lpNorm f 6 μ ^ 2) := by
  rw [ENNReal.ofReal_pow lpNorm_nonneg, ofReal_lpNorm hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num only [show (6 : ℝ)⁻¹ * 2 = 1 / 3 by norm_num]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hf0] with x hx
  rw [Real.enorm_of_nonneg hx]

/-- Squaring a real Sobolev estimate supplies precisely the input of the mixed
energy theorem. Finiteness of the L6 norm is required, not inferred from a real
norm that could have been defined as zero on non-integrable functions. -/
theorem lintegral_ofReal_six_rpow_le_of_lpNorm_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 6 μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    {a b E D : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hbound : lpNorm f 6 μ ≤ a * E + b * Real.sqrt D) :
    (∫⁻ x, (ENNReal.ofReal (f x)) ^ (6 : ℝ) ∂μ) ^ (1 / 3 : ℝ) ≤
      ENNReal.ofReal (2 * a ^ 2) * ENNReal.ofReal E ^ 2 +
        ENNReal.ofReal (2 * b ^ 2) * ENNReal.ofReal D := by
  rw [lintegral_ofReal_six_rpow_eq_lpNorm_sq hf hf0]
  have hsq : lpNorm f 6 μ ^ 2 ≤ 2 * a ^ 2 * E ^ 2 + 2 * b ^ 2 * D := by
    have hn := lpNorm_nonneg (f := f) (p := 6) (μ := μ)
    have hbd : 0 ≤ a * E + b * Real.sqrt D := by positivity
    have h1 := sq_le_sq₀ hn hbd |>.mpr hbound
    have h2 := sq_nonneg (a * E - b * Real.sqrt D)
    have h3 := Real.sq_sqrt hD
    nlinarith
  calc
    _ ≤ ENNReal.ofReal (2 * a ^ 2 * E ^ 2 + 2 * b ^ 2 * D) := ENNReal.ofReal_le_ofReal hsq
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (show 0 ≤ 2 * a ^ 2 by positivity),
        ENNReal.ofReal_mul (show 0 ≤ 2 * b ^ 2 by positivity),
        ENNReal.ofReal_pow hE]

end PDE
