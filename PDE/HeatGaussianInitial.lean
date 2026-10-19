import PDE.HeatGaussian
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Initial-value limit of the Gaussian

Parabolic scaling reduces Gaussian pairings to an integral against the fixed
integrable density at time one. Dominated convergence then proves convergence
to evaluation at the origin for bounded continuous space–time test functions.
Tests depending only on space follow as a special case. Translation
provides the corresponding initial-value limit for convolution at every point.
No spatial integrability assumption on the bounded initial function is needed.
-/

open MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators

namespace PDE

/-- Parabolic scaling of the normalized heat kernel. -/
theorem heatGaussian_scale {n : ℕ} {r : ℝ} (hr : 0 < r) (x : Space n) :
    heatGaussian (r ^ 2) (r • x) = (r ^ n)⁻¹ * heatGaussian 1 x := by
  have hs : Real.sqrt (4 * Real.pi * r ^ 2) = Real.sqrt (4 * Real.pi) * r := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hr.le]
  simp only [heatGaussian, heatGaussianFactor, Pi.smul_apply, smul_eq_mul, hs,
    mul_one, mul_inv_rev, mul_pow, inv_pow]
  have he : -(r ^ 2 * ∑ i, x i ^ 2) / (4 * r ^ 2) = -(∑ i, x i ^ 2) / 4 := by
    field_simp
  rw [← Finset.mul_sum, he]
  ring

/-- Rescale a Gaussian pairing to a fixed, integrable Gaussian. -/
theorem integral_heatGaussian_scale {n : ℕ} {r : ℝ} (hr : 0 < r) (f : Space n → ℝ) :
    (∫ x, heatGaussian (r ^ 2) x * f x) =
      ∫ x, heatGaussian 1 x * f (r • x) := by
  have h := Measure.integral_comp_smul_of_nonneg volume
    (fun x : Space n => heatGaussian (r ^ 2) x * f x) r (hR := hr.le)
  simp only [Space, Module.finrank_fin_fun, smul_eq_mul, heatGaussian_scale hr,
    mul_assoc, integral_const_mul] at h
  exact (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ hr.ne')) h).symm

/-- The initial Dirac limit also permits joint dependence of the test on time
and space, as needed for the fundamental-solution identity. -/
theorem heatGaussian_tendsto_initial_joint {n : ℕ} {f : ℝ × Space n → ℝ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ p, ‖f p‖ ≤ C) :
    Tendsto (fun t : ℝ => ∫ x, heatGaussian t x * f (t, x))
      (𝓝[>] 0) (𝓝 (f (0, 0))) := by
  have hK : Integrable (heatGaussian (n := n) 1) := heatGaussian_integrable zero_lt_one
  have hKc : Continuous (heatGaussian (n := n) 1) :=
    (heatGaussian_contDiff_space 1).continuous
  have hs : Tendsto Real.sqrt (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa using Real.continuous_sqrt.tendsto 0
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (Space n))) (l := 𝓝 (0 : ℝ))
    (F := fun t x => heatGaussian 1 x * f (t, Real.sqrt t • x))
    (f := fun x => heatGaussian 1 x * f (0, 0))
    (fun x => heatGaussian 1 x * C)
    (Eventually.of_forall fun t => by
      apply Continuous.aestronglyMeasurable
      fun_prop)
    (Eventually.of_forall fun t => ae_of_all _ fun x => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (heatGaussian_pos zero_lt_one x)]
      exact mul_le_mul_of_nonneg_left (hC _) (heatGaussian_pos zero_lt_one x).le)
    (hK.mul_const C)
    (ae_of_all _ fun x => by
      apply tendsto_const_nhds.mul
      apply hf.continuousAt.tendsto.comp
      simpa using tendsto_id.prodMk_nhds (hs.smul_const x))
  have h' : Tendsto (fun t : ℝ => ∫ x, heatGaussian 1 x * f (t, Real.sqrt t • x))
      (𝓝[>] 0) (𝓝 (f (0, 0))) := by
    simpa only [integral_mul_const, heatGaussian_integral zero_lt_one, one_mul] using
      h.mono_left nhdsWithin_le_nhds
  apply h'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [← integral_heatGaussian_scale (Real.sqrt_pos.mpr ht) (fun x => f (t, x)),
    Real.sq_sqrt ht.le]

/-- The Gaussian has initial value a unit point mass, tested against bounded
continuous functions, in every spatial dimension. -/
theorem heatGaussian_tendsto_initial {n : ℕ} {f : Space n → ℝ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun t : ℝ => ∫ x, heatGaussian t x * f x)
      (𝓝[>] 0) (𝓝 (f 0)) := by
  exact heatGaussian_tendsto_initial_joint (f := fun p => f p.2)
    (hf.comp continuous_snd) (fun p => hC p.2)

/-- Pairings used in the initial-value limit are genuine integrable functions. -/
theorem heatGaussian_integrable_mul {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : Space n → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun x => heatGaussian t x * f x) := by
  apply ((heatGaussian_integrable (n := n) ht).mul_const C).mono'
  · apply Continuous.aestronglyMeasurable
    have : Continuous (heatGaussian (n := n) t) := (heatGaussian_contDiff_space t).continuous
    fun_prop
  · filter_upwards with x
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (heatGaussian_pos ht x)]
    exact mul_le_mul_of_nonneg_left (hC x) (heatGaussian_pos ht x).le

/-- Gaussian convolution recovers bounded continuous initial data at every point. -/
theorem heatGaussian_convolution_tendsto_initial {n : ℕ} {f : Space n → ℝ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) (x : Space n) :
    Tendsto (fun t : ℝ => ∫ y, heatGaussian t (x - y) * f y)
      (𝓝[>] 0) (𝓝 (f x)) := by
  have h := heatGaussian_tendsto_initial (f := fun y => f (x - y))
    (by fun_prop) (fun y => hC (x - y))
  have heq (t : ℝ) : (∫ y, heatGaussian t y * f (x - y)) =
      ∫ y, heatGaussian t (x - y) * f y := by
    simpa only [sub_sub_cancel] using
      (integral_sub_left_eq_self
        (fun y => heatGaussian t y * f (x - y)) volume x).symm
  simpa only [heq, sub_zero] using h

end PDE
