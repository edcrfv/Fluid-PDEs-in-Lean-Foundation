import PDE.HeatGaussianCausal
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Space–time integrability of the causal Gaussian

Unit spatial mass bounds the integral on every finite time strip. The Gaussian's
zero values at nonpositive times (in positive spatial dimension) then give local
integrability on all of space–time, including its singular source. Continuous
compactly supported test factors produce absolutely integrable pairings.
-/

open MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators

namespace PDE

/-- Integrability across time zero on every finite time strip. -/
theorem heatGaussian_integrableOn_strip {n : ℕ} (hn : 0 < n) (a b : ℝ) :
    IntegrableOn (fun p : ℝ × Space n => heatGaussian p.1 p.2)
      (Icc a b ×ˢ univ) := by
  have hm : Measurable (fun p : ℝ × Space n => heatGaussian p.1 p.2) := by
    unfold heatGaussian heatGaussianFactor
    fun_prop
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.restrict_prod_eq_prod_univ]
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · apply ae_of_all
    intro t
    by_cases ht : 0 < t
    · exact heatGaussian_integrable ht
    · simp only [heatGaussian_eq_zero_of_nonpos hn (le_of_not_gt ht)]
      exact integrable_zero _ _ _
  · have he (t : ℝ) : (∫ x : Space n, ‖heatGaussian t x‖) = if 0 < t then 1 else 0 := by
      by_cases ht : 0 < t
      · simp only [Real.norm_eq_abs, abs_of_pos (heatGaussian_pos ht _), ite_eq_left ht,
          heatGaussian_integral ht]
      · simp only [heatGaussian_eq_zero_of_nonpos hn (le_of_not_gt ht), norm_zero,
          integral_zero, ite_eq_right ht]
    simp only [he]
    apply (integrableOn_const (s := Icc a b) (μ := volume) (C := (1 : ℝ)) isCompact_Icc.measure_lt_top.ne).mono'
    · apply Measurable.aestronglyMeasurable
      exact measurable_const.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    · apply ae_of_all
      intro t
      split_ifs <;> norm_num

/-- The causal Gaussian is locally integrable on the full space–time space. -/
theorem heatGaussian_locallyIntegrable {n : ℕ} (hn : 0 < n) :
    LocallyIntegrable (fun p : ℝ × Space n => heatGaussian p.1 p.2) volume := by
  apply locallyIntegrable_iff.2
  intro K hK
  obtain ⟨R, _, hR⟩ := hK.isBounded.exists_pos_norm_le
  apply (heatGaussian_integrableOn_strip hn (-R) R).mono_set
  intro p hp
  have hb := (norm_fst_le p).trans (hR p hp)
  exact ⟨abs_le.mp hb, mem_univ _⟩

/-- Multiplying the causal kernel by a continuous compactly supported test gives
an absolutely integrable function on space–time. -/
theorem heatGaussian_integrable_test {n : ℕ} (hn : 0 < n) {φ : ℝ × Space n → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun p : ℝ × Space n => heatGaussian p.1 p.2 * φ p) := by
  exact (heatGaussian_locallyIntegrable hn).integrable_smul_right_of_hasCompactSupport hφ hc

end PDE
