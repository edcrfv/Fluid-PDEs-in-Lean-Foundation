import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! A weighted three-factor Hölder estimate. All integrals are extended-valued,
so the statement does not silently discard a divergent integral. No positive
lower bound on the weight is required. -/

open MeasureTheory
open scoped ENNReal

namespace PDE

/-- The gain in the density-weighted three-dimensional interpolation estimate. -/
noncomputable def densityInterpolationGain (p : ℝ) : ℝ := 2 * (p - 3) / (3 * (p - 1))

theorem densityInterpolationGain_pos {p : ℝ} (hp : 3 < p) :
    0 < densityInterpolationGain p := by
  unfold densityInterpolationGain
  exact div_pos (mul_pos (by norm_num) (by linarith))
    (mul_pos (by norm_num) (by linarith))

theorem densityInterpolationGain_lt_two_thirds {p : ℝ} (hp : 3 < p) :
    densityInterpolationGain p < 2 / 3 := by
  unfold densityInterpolationGain
  rw [div_lt_iff₀ (by linarith : 0 < 3 * (p - 1))]
  linarith

theorem densityInterpolationGain_holder {p : ℝ} (hp : 3 < p) :
    densityInterpolationGain p + 1 / 3 + (2 - densityInterpolationGain p) / p = 1 := by
  unfold densityInterpolationGain
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  field_simp [hp0, hp1]
  ring

/-- The spatial estimate underlying the superlinear pressure bound. In particular
`ρ = 0` is allowed, and finiteness is a conclusion when the right side is finite. -/
theorem lintegral_density_weighted_interpolation
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {ρ f : α → ℝ≥0∞}
    (hρ : AEMeasurable ρ μ) (hf : AEMeasurable f μ) {p : ℝ} (hp : 3 < p) :
    (∫⁻ x, ρ x ^ (2 : ℝ) * f x ^ (2 + densityInterpolationGain p) ∂μ) ≤
      (∫⁻ x, ρ x * f x ∂μ) ^ densityInterpolationGain p *
      (∫⁻ x, f x ^ (6 : ℝ) ∂μ) ^ (1 / 3 : ℝ) *
      (∫⁻ x, ρ x ^ p ∂μ) ^ ((2 - densityInterpolationGain p) / p) := by
  let r := densityInterpolationGain p
  have hr : 0 ≤ r := (densityInterpolationGain_pos hp).le
  have hr2 : 0 ≤ 2 - r := by
    have := densityInterpolationGain_lt_two_thirds hp
    dsimp [r]
    linarith
  let F : Fin 3 → α → ℝ≥0∞ := ![fun x => ρ x * f x, fun x => f x ^ (6 : ℝ),
    fun x => ρ x ^ p]
  let w : Fin 3 → ℝ := ![r, 1 / 3, (2 - r) / p]
  have hF : ∀ i ∈ Finset.univ, AEMeasurable (F i) μ := by
    intro i _
    fin_cases i
    · exact hρ.mul hf
    · exact hf.pow_const _
    · exact hρ.pow_const _
  have hw : ∑ i ∈ Finset.univ, w i = 1 := by
    simpa [w, r, Fin.sum_univ_succ, add_assoc] using densityInterpolationGain_holder hp
  have hw0 : ∀ i ∈ Finset.univ, 0 ≤ w i := by
    intro i _
    fin_cases i
    · exact hr
    · norm_num [w]
    · exact div_nonneg hr2 (by linarith)
  have h := ENNReal.lintegral_prod_norm_pow_le Finset.univ hF hw hw0
  simp only [F, w, Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.prod_univ_zero, mul_one] at h
  have hid (a b : ℝ≥0∞) :
      (a * b) ^ r * (b ^ (6 : ℝ)) ^ (1 / 3 : ℝ) *
        (a ^ p) ^ ((2 - r) / p) = a ^ (2 : ℝ) * b ^ (2 + r) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul]
    have hexp : p * ((2 - r) / p) = 2 - r := by
      field_simp
    norm_num only [show (6 : ℝ) * (1 / 3) = 2 by norm_num, hexp]
    calc
      _ = (a ^ r * a ^ (2 - r)) * (b ^ (2 : ℝ) * b ^ r) := by ring
      _ = a ^ (r + (2 - r)) * b ^ (2 + r) := by
        rw [ENNReal.rpow_add_of_nonneg r (2 - r) hr hr2,
          ENNReal.rpow_add_of_nonneg 2 r (by norm_num) hr]
      _ = _ := by congr 2; ring
  simpa only [mul_assoc, ← mul_assoc, hid] using h

end PDE
