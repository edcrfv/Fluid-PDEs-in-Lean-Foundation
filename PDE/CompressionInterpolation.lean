import PDE.WeightedInterpolation
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Mixed space/time interpolation for density compression. The spatial
exponent is strictly above three; no positive lower density is required. -/

open MeasureTheory
open scoped ENNReal

namespace PDE

theorem lintegral_rpow_le_measure_add {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ≥0∞} {p q : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p) :
    (∫⁻ x, f x ^ q ∂μ) ≤ μ Set.univ + ∫⁻ x, f x ^ p ∂μ := by
  calc
    _ ≤ ∫⁻ x, 1 + f x ^ p ∂μ := by
      apply lintegral_mono
      intro x
      rcases le_total (f x) 1 with hx | hx
      · have hh : f x ^ q ≤ 1 := by
          simpa using ENNReal.rpow_le_rpow_of_exponent_ge hx hq
        exact hh.trans (le_add_right le_rfl)
      · exact (ENNReal.rpow_le_rpow_of_exponent_le hx hqp).trans (le_add_left le_rfl)
    _ = _ := by rw [lintegral_add_left measurable_const, lintegral_one]

/-- Fourth moments interpolate between a spatial p-moment and the squared
spatial L⁶ norm. The latter only needs an L¹ bound in time. -/
theorem lintegral_fourth_le_mixed_density
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {ρ : α × β → ℝ≥0∞} (hρ : Measurable ρ) {p b q : ℝ}
    (hb : 0 ≤ b) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hsum : b + q / 3 = 1) (hexp : p * b + 2 * q = 4)
    {R : ℝ≥0∞} (hmoment : ∀ᵐ t ∂μ, (∫⁻ x, ρ (t, x) ^ p ∂ν) ≤ R) :
    (∫⁻ z, ρ z ^ (4 : ℝ) ∂μ.prod ν) ≤
      R ^ b * (∫⁻ t, (∫⁻ x, ρ (t, x) ^ (6 : ℝ) ∂ν) ^ (1 / 3 : ℝ) ∂μ) ^ q *
        (μ Set.univ) ^ (1 - q) := by
  let L : α → ℝ≥0∞ := fun t => (∫⁻ x, ρ (t, x) ^ (6 : ℝ) ∂ν) ^ (1 / 3 : ℝ)
  have hL : Measurable L := (hρ.pow_const (6 : ℝ)).lintegral_prod_right.pow_const _
  have hs : ∀ᵐ t ∂μ, (∫⁻ x, ρ (t, x) ^ (4 : ℝ) ∂ν) ≤ R ^ b * L t ^ q := by
    filter_upwards [hmoment] with t ht
    have hm : Measurable (fun x => ρ (t, x)) :=
      hρ.comp (measurable_const.prodMk measurable_id)
    have hh := ENNReal.lintegral_mul_norm_pow_le (μ := ν)
      (hm.pow_const p).aemeasurable (hm.pow_const (6 : ℝ)).aemeasurable
      hb (show 0 ≤ q / 3 by positivity) hsum
    have hid (z : ℝ≥0∞) : (z ^ p) ^ b * (z ^ (6 : ℝ)) ^ (q / 3) = z ^ (4 : ℝ) := by
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      have hp : 0 ≤ p * b := by nlinarith
      rw [← ENNReal.rpow_add_of_nonneg _ _ hp (by positivity)]
      congr 1
      linarith
    simp_rw [hid] at hh
    apply hh.trans
    have hpow : (∫⁻ x, ρ (t, x) ^ (6 : ℝ) ∂ν) ^ (q / 3) = L t ^ q := by
      dsimp [L]
      rw [← ENNReal.rpow_mul]
      congr 1
      ring
    rw [hpow]
    exact mul_le_mul_left (ENNReal.rpow_le_rpow ht hb) _
  rw [lintegral_prod _ (hρ.pow_const (4 : ℝ)).aemeasurable]
  calc
    _ ≤ ∫⁻ t, R ^ b * L t ^ q ∂μ := lintegral_mono_ae hs
    _ = R ^ b * ∫⁻ t, L t ^ q ∂μ := lintegral_const_mul'' _ (hL.pow_const q).aemeasurable
    _ ≤ R ^ b * ((∫⁻ t, L t ∂μ) ^ q * (μ Set.univ) ^ (1 - q)) := by
      apply mul_le_mul_right
      have hh := ENNReal.lintegral_mul_norm_pow_le (μ := μ) hL.aemeasurable
        (measurable_const (a := (1 : ℝ≥0∞))).aemeasurable hq (by linarith : 0 ≤ 1 - q)
        (by ring : q + (1 - q) = 1)
      simpa only [ENNReal.one_rpow, mul_one, lintegral_const, one_mul] using hh
    _ = _ := mul_assoc _ _ _ |>.symm

theorem compression_interpolation_exponents {p : ℝ} (hp : 3 < p) (hp4 : p ≤ 4) :
    0 ≤ 2 / (6 - p) ∧ 0 ≤ 3 * (4 - p) / (6 - p) ∧
      3 * (4 - p) / (6 - p) < 1 ∧
      2 / (6 - p) + (3 * (4 - p) / (6 - p)) / 3 = 1 ∧
      p * (2 / (6 - p)) + 2 * (3 * (4 - p) / (6 - p)) = 4 := by
  have hd : 0 < 6 - p := by linarith
  refine ⟨by positivity, div_nonneg (by linarith) hd.le, ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ hd]
    linarith
  · field_simp
    ring
  · field_simp
    ring

/-- Actual compression work, including its integrability, follows from density
moments, mixed L²(time; L⁶(space)) control, and an L² divergence bound. -/
theorem integral_abs_compression_le_of_mixed_bounds
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [SFinite ν]
    {ρ d : α × β → ℝ} (hρ : Measurable ρ) (hd : Measurable d)
    {p b q R S D E : ℝ} (hb : 0 ≤ b) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hsum : b + q / 3 = 1) (hexp : p * b + 2 * q = 4)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hmoment : ∀ᵐ t ∂μ, (∫⁻ x, ENNReal.ofReal |ρ (t, x)| ^ p ∂ν) ≤ ENNReal.ofReal R)
    (hsix : (∫⁻ t, (∫⁻ x, ENNReal.ofReal |ρ (t, x)| ^ (6 : ℝ) ∂ν) ^ (1 / 3 : ℝ) ∂μ) ≤
      ENNReal.ofReal (S * (1 + E)))
    (hdiv : (∫⁻ z, ENNReal.ofReal |d z| ^ (2 : ℝ) ∂μ.prod ν) ≤ ENNReal.ofReal D) :
    Integrable (fun z => |ρ z ^ 2 * d z|) (μ.prod ν) ∧
      (∫ z, |ρ z ^ 2 * d z| ∂μ.prod ν) ≤
        R ^ (b / 2) * S ^ (q / 2) * D ^ (1 / 2 : ℝ) *
          (μ Set.univ).toReal ^ ((1 - q) / 2) * (1 + E) ^ (q / 2) := by
  let F := fun z => ENNReal.ofReal |ρ z|
  let H := fun z => ENNReal.ofReal |d z|
  have hF : Measurable F := hρ.norm.ennreal_ofReal
  have hH : Measurable H := hd.norm.ennreal_ofReal
  let U := ENNReal.ofReal R ^ b * ENNReal.ofReal (S * (1 + E)) ^ q *
    (μ Set.univ) ^ (1 - q)
  have h4 : (∫⁻ z, F z ^ (4 : ℝ) ∂μ.prod ν) ≤ U := by
    apply (lintegral_fourth_le_mixed_density hF hb hq hq1 hsum hexp hmoment).trans
    dsimp [U]
    gcongr
  have hwork : (∫⁻ z, ENNReal.ofReal |ρ z ^ 2 * d z| ∂μ.prod ν) ≤
      U ^ (1 / 2 : ℝ) * ENNReal.ofReal D ^ (1 / 2 : ℝ) := by
    have hh := ENNReal.lintegral_mul_norm_pow_le (μ := μ.prod ν) (hF.pow_const (4 : ℝ)).aemeasurable
      (hH.pow_const (2 : ℝ)).aemeasurable
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have hid (z : α × β) : (F z ^ (4 : ℝ)) ^ (1 / 2 : ℝ) *
        (H z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = ENNReal.ofReal |ρ z ^ 2 * d z| := by
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num only [show (4 : ℝ) * (1 / 2) = 2 by norm_num,
        show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_two]
      simp only [F, H, abs_mul, abs_pow, ENNReal.ofReal_mul (sq_nonneg _),
        ENNReal.ofReal_pow (abs_nonneg _)]
    simp_rw [hid] at hh
    exact hh.trans (mul_le_mul' (ENNReal.rpow_le_rpow h4 (by norm_num))
      (ENNReal.rpow_le_rpow hdiv (by norm_num)))
  have hUt : U ≠ ∞ := by
    dsimp [U]
    finiteness
  have htop : U ^ (1 / 2 : ℝ) * ENNReal.ofReal D ^ (1 / 2 : ℝ) ≠ ∞ := by finiteness
  have hi : Integrable (fun z => |ρ z ^ 2 * d z|) (μ.prod ν) :=
    (lintegral_ofReal_ne_top_iff_integrable ((hρ.pow_const 2).mul hd).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => abs_nonneg _)).mp (ne_top_of_le_ne_top htop hwork)
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun z => abs_nonneg _)] at hwork
  have hh := ENNReal.toReal_mono htop hwork
  rw [ENNReal.toReal_ofReal (integral_nonneg fun z => abs_nonneg _)] at hh
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hD] at hh
  have he : U.toReal ^ (1 / 2 : ℝ) * D ^ (1 / 2 : ℝ) =
      R ^ (b / 2) * S ^ (q / 2) * D ^ (1 / 2 : ℝ) *
        (μ Set.univ).toReal ^ ((1 - q) / 2) * (1 + E) ^ (q / 2) := by
    dsimp [U]
    simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hR,
      ENNReal.toReal_ofReal (mul_nonneg hS (by linarith : 0 ≤ 1 + E))]
    rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg hR _) (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg ENNReal.toReal_nonneg _),
      Real.mul_rpow (Real.rpow_nonneg hR _) (Real.rpow_nonneg (by positivity) _),
      ← Real.rpow_mul hR, ← Real.rpow_mul (by positivity : 0 ≤ S * (1 + E)),
      ← Real.rpow_mul ENNReal.toReal_nonneg,
      Real.mul_rpow hS (by linarith : 0 ≤ 1 + E)]
    simp only [mul_one_div]
    ring
  exact hh.trans_eq he

end PDE
