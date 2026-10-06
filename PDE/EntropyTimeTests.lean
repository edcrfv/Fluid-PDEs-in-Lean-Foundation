import PDE.IntervalPositiveDistribution

/-! Backward primitive tests that retain the initial entropy and vanish
strictly before the final time. A compact spatially constant time test is
constructed explicitly; no discontinuous time indicator is substituted. -/

open MeasureTheory Set Filter Metric
open scoped ContDiff Topology

namespace PDE

/-- A nonnegative smooth interior test is minus the derivative, on the
physical interval, of a legal nonnegative initial-value entropy test. -/
theorem exists_backward_entropy_test {T : ℝ} (hT : 0 < T) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ioo 0 T) (hn : ∀ t, 0 ≤ g t) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ Iio T ∧ (∀ t, 0 ≤ φ t) ∧ φ T = 0 ∧
      (∀ t ∈ Icc 0 T, HasDerivAt φ (-g t) t) := by
  let K := tsupport g ∪ {T / 2}
  have hK : IsCompact K := hc.isCompact.union isCompact_singleton
  obtain ⟨d, hd⟩ := hK.exists_isGreatest (show K.Nonempty from ⟨T / 2, Or.inr rfl⟩)
  have hdT : d < T := by
    rcases hd.1 with hd | hd
    · exact (hs hd).2
    · have he : d = T / 2 := hd
      linarith
  obtain ⟨e, hde, heT⟩ := exists_between hdT
  have hge (y : ℝ) (hy : e ≤ y) : g y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hy' => by
      have hh := hd.2 (Or.inl hy')
      linarith)
  let ψ := fun t => -(∫ s in T..t, g s)
  have hdψ (t : ℝ) : HasDerivAt ψ (-g t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hg.continuous.intervalIntegrable T t)
      (hg.continuous.stronglyMeasurableAtFilter volume (𝓝 t)) hg.continuous.continuousAt).neg
  have hψ : ContDiff ℝ ∞ ψ := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun t => (hdψ t).differentiableAt, ?_⟩
    have heq : deriv ψ = fun t => -g t := funext fun t => (hdψ t).deriv
    rw [heq]
    exact hg.neg
  have htail (t : ℝ) (ht : e ≤ t) : ψ t = 0 := by
    have hz : (∫ s in T..t, g s) = 0 := by
      calc
        _ = ∫ _s in T..t, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs'
          exact hge s ((le_min heT.le ht).trans hs'.1)
        _ = 0 := by simp
    simp only [ψ, hz, neg_zero]
  have hψn (t : ℝ) : 0 ≤ ψ t := by
    by_cases ht : t ≤ T
    · change 0 ≤ -(∫ s in T..t, g s)
      rw [intervalIntegral.integral_symm, neg_neg]
      exact intervalIntegral.integral_nonneg ht (fun t _ => hn t)
    · rw [htail t (heT.le.trans (le_of_not_ge ht))]
  let χ : ContDiffBump (0 : ℝ) := ⟨T + 1, T + 2, by linarith, by linarith⟩
  let φ := fun t => χ t * ψ t
  have hχ1 (t : ℝ) (ht : t ∈ Icc 0 T) : (fun s => χ s) =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    apply χ.eventuallyEq_one_of_mem_ball
    change dist t 0 < T + 1
    rw [dist_zero_right, Real.norm_of_nonneg ht.1]
    linarith [ht.2]
  have hsψ : tsupport ψ ⊆ Iic e := by
    apply closure_minimal _ isClosed_Iic
    intro t ht
    by_contra h
    exact ht (htail t (le_of_not_ge h))
  refine ⟨φ, χ.contDiff.mul hψ, χ.hasCompactSupport.mul_right, ?_,
    fun t => mul_nonneg χ.nonneg (hψn t), ?_, ?_⟩
  · exact tsupport_mul_subset_right.trans (hsψ.trans (Iic_subset_Iio.mpr heT))
  · simp only [φ, htail T heT.le, mul_zero]
  · intro t ht
    have hdχ : HasDerivAt (fun s => χ s) 0 t :=
      (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq (hχ1 t ht)
    have hh := hdχ.mul (hdψ t)
    change HasDerivAt φ (0 * ψ t + χ t * (-g t)) t at hh
    simpa only [zero_mul, (hχ1 t ht).self_of_nhds, one_mul, zero_add] using hh

end PDE
