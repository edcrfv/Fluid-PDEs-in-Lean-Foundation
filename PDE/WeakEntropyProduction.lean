import PDE.EntropyTimeTests
import PDE.TimePrimitive

/-! Cumulative entropy production from legal weak initial-value tests.
Entropy is only integrable in time. The inequality allows additional positive
production, including singular defects; no AC representative is assumed. -/

open MeasureTheory Set
open scoped ContDiff

namespace PDE

/-- Ordinary smooth nonnegative time tests compactly supported below T.
They may be nonzero at the initial time. -/
structure IsInitialTimeTest (T : ℝ) (φ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  compact : HasCompactSupport φ
  support_before_terminal : tsupport φ ⊆ Iio T
  nonneg : ∀ t, 0 ≤ φ t

/-- The spatially integrated weak entropy inequality with its actual initial
entropy and an integrable lower bound on production. -/
structure HasWeakEntropyProduction (T S₀ : ℝ) (S q : ℝ → ℝ) : Prop where
  entropy_integrable : IntegrableOn S (Icc 0 T)
  production_integrable : IntegrableOn q (Icc 0 T)
  test : ∀ φ, IsInitialTimeTest T φ →
    (∫ t in Icc 0 T, deriv φ t * S t) + (∫ t in Icc 0 T, φ t * q t) ≤ -φ 0 * S₀

/-- Legal smooth tests imply the cumulative initial entropy inequality a.e.
No entropy trace at an arbitrarily prescribed positive terminal time is used. -/
theorem HasWeakEntropyProduction.cumulative_bound {T S₀ : ℝ} {S q : ℝ → ℝ}
    (h : HasWeakEntropyProduction T S₀ S q) (hT : 0 < T) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T), S₀ + (∫ s in Icc 0 t, q s) ≤ S t := by
  let P := timePrimitive 0 S₀ q
  have hPc : ContinuousOn P (Icc 0 T) := timePrimitive_continuousOn S₀ h.production_integrable
  have hPi : IntegrableOn P (Icc 0 T) := hPc.integrableOn_Icc
  have hnonneg : ∀ᵐ t ∂volume.restrict (Icc 0 T), 0 ≤ S t - P t := by
    apply ae_nonneg_of_interval_smooth_tests (h.entropy_integrable.sub hPi)
    intro g hg hc hs hn
    obtain ⟨φ, hφ, hcφ, hsφ, hnφ, hφT, hdφ⟩ := exists_backward_entropy_test hT hg hc hs hn
    have ht := h.test φ ⟨hφ, hcφ, hsφ, hnφ⟩
    have hp := timePrimitive_integrated hT.le S₀ h.production_integrable φ (deriv φ)
      (fun t => (hφ.differentiable (by simp) t).hasDerivAt)
      (hφ.continuous_deriv (by simp)) hφT
    change (∫ t in Icc 0 T, deriv φ t * P t) + (∫ t in Icc 0 T, φ t * q t) = -φ 0 * S₀ at hp
    have he (F : ℝ → ℝ) : (∫ t in Icc 0 T, deriv φ t * F t) =
        -(∫ t in Icc 0 T, g t * F t) := by
      rw [← integral_neg]
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      change deriv φ t * F t = -(g t * F t)
      rw [(hdφ t ht).deriv, neg_mul]
    rw [he S] at ht
    rw [he P] at hp
    have hgS : IntegrableOn (fun t => g t * S t) (Icc 0 T) :=
      h.entropy_integrable.continuousOn_smul hg.continuous.continuousOn isCompact_Icc
    have hgP : IntegrableOn (fun t => g t * P t) (Icc 0 T) :=
      hPi.continuousOn_smul hg.continuous.continuousOn isCompact_Icc
    change 0 ≤ ∫ t in Icc 0 T, g t * (S t - P t)
    simp_rw [mul_sub]
    rw [integral_sub hgS hgP]
    linarith
  exact hnonneg.mono fun _ ht => sub_nonneg.mp ht

/-- The weak conservation identity, tested only by ordinary nonnegative
initial-value tests, fixes the conserved quantity to its initial value a.e. -/
theorem ae_eq_initial_of_weak_conservation {T m : ℝ} {M : ℝ → ℝ}
    (hT : 0 < T) (hi : IntegrableOn M (Icc 0 T))
    (hw : ∀ φ, IsInitialTimeTest T φ →
      (∫ t in Icc 0 T, deriv φ t * M t) = -φ 0 * m) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T), M t = m := by
  have hp : HasWeakEntropyProduction T m M (fun _ => 0) :=
    ⟨hi, integrable_const 0, fun φ hφ => by simpa using (hw φ hφ).le⟩
  have hn : HasWeakEntropyProduction T (-m) (fun t => -M t) (fun _ => 0) := by
    refine ⟨hi.neg, integrable_const 0, fun φ hφ => ?_⟩
    simp only [mul_zero, integral_zero, add_zero, mul_neg, integral_neg, hw φ hφ]
    exact le_rfl
  filter_upwards [hp.cumulative_bound hT, hn.cumulative_bound hT] with t ht ht'
  simp only [integral_zero, add_zero] at ht ht'
  linarith

/-- A positive entropy jump satisfies the weak inequality with zero ordinary
production. This verifies that the interface permits singular positive defects
and does not impose an absolutely continuous entropy trajectory. -/
theorem hasWeakEntropyProduction_step {T τ c : ℝ}
    (hτ : 0 < τ) (hτT : τ < T) (hc : 0 ≤ c) :
    HasWeakEntropyProduction T 0 ((Ici τ).indicator (fun _ : ℝ => c)) (fun _ => 0) := by
  refine ⟨(integrable_const c).indicator measurableSet_Ici, integrable_const 0, ?_⟩
  intro φ hφ
  simp only [mul_zero, integral_zero, add_zero]
  have he : (fun t => deriv φ t * (Ici τ).indicator (fun _ : ℝ => c) t) =
      (Ici τ).indicator (fun t => deriv φ t * c) := by
    funext t
    by_cases ht : t ∈ Ici τ <;> simp [ht]
  rw [he, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have hsets : Ici τ ∩ Icc (0 : ℝ) T = Icc τ T := by
    ext t
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · exact fun ht => ⟨ht.1, ht.2.2⟩
    · exact fun ht => ⟨ht.1, hτ.le.trans ht.1, ht.2⟩
  rw [hsets, integral_mul_const]
  have hφT : φ T = 0 := image_eq_zero_of_notMem_tsupport
    (fun ht => (show T < T from hφ.support_before_terminal ht).false)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ht : t ∈ uIcc τ T) => (hφ.smooth.differentiable (by simp) t).hasDerivAt)
    ((hφ.smooth.continuous_deriv (by simp)).intervalIntegrable (μ := volume) τ T)
  rw [intervalIntegral.integral_of_le hτT.le, ← integral_Icc_eq_integral_Ioc, hφT, zero_sub] at hFTC
  rw [hFTC]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hφ.nonneg τ)) hc

end PDE
