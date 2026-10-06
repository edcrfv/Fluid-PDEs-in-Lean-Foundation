import PDE.MeanPoincare
import PDE.AbsoluteContinuity

/-!
# Mean Poincaré for weak differentiation on an interval

We reconstruct an absolutely continuous representative from the existing
`HasL2TimeDerivative` weak identity, without prescribing an initial trace.
The interval is spatial in the Poincaré application. The name of the reused
L² interface does not impose a time-evolution equation or a boundary value.

This does not yet identify the higher-dimensional `H1` graph with functions
that are absolutely continuous on almost every coordinate line.
-/

open MeasureTheory Set
open scoped ENNReal

namespace PDE

/-- A function whose weak derivative vanishes is a.e. its mean on the interval.
Only the tests, not the function itself, vanish at the endpoints. -/
theorem ae_eq_mean_of_weak_derivative_zero {a b : ℝ} (hab : a < b) {w : ℝ → ℝ}
    (hw : IntegrableOn w (Icc a b))
    (hweak : ∀ (η η' : ℝ → ℝ), (∀ t, HasDerivAt η (η' t) t) → Continuous η' →
      η a = 0 → η b = 0 → (∫ t in Icc a b, η' t * w t) = 0) :
    w =ᵐ[volume.restrict (Icc a b)] fun _ => (∫ t in Icc a b, w t) / (b - a) := by
  let c := (∫ t in Icc a b, w t) / (b - a)
  have hvol : (volume.restrict (Icc a b)).real univ = b - a := by
    simp [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  have hdiff : IntegrableOn (fun t => w t - c) (Icc a b) := hw.sub (integrable_const c)
  have hz : ∀ᵐ t ∂volume, t ∈ Ioo a b → w t - c = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hdiff.mono_set Ioo_subset_Icc_self).locallyIntegrableOn)
    intro φ hφ _hc hs
    let m := (∫ t in Icc a b, φ t) / (b - a)
    let ψ := fun t => φ t - m
    let η := fun t => ∫ s in a..t, ψ s
    have hψ : Continuous ψ := hφ.continuous.sub continuous_const
    have hη : ∀ t, HasDerivAt η (ψ t) t := fun t =>
      intervalIntegral.integral_hasDerivAt_right (hψ.intervalIntegrable a t)
        (hψ.stronglyMeasurableAtFilter volume (nhds t)) hψ.continuousAt
    have hηa : η a = 0 := by simp [η]
    have hηb : η b = 0 := by
      simp only [η, intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc]
      change (∫ t in Icc a b, φ t - m) = 0
      rw [integral_sub hφ.continuous.integrableOn_Icc (integrable_const m),
        integral_const, smul_eq_mul, hvol]
      dsimp [m]
      rw [mul_div_cancel₀ _ (sub_pos.mpr hab).ne', sub_self]
    have htest := hweak η ψ hη hψ hηa hηb
    have hφw : IntegrableOn (fun t => φ t * w t) (Icc a b) :=
      hw.continuousOn_mul hφ.continuous.continuousOn isCompact_Icc
    have htest' : (∫ t in Icc a b, φ t * w t) = m * (∫ t in Icc a b, w t) := by
      change (∫ t in Icc a b, (φ t - m) * w t) = 0 at htest
      simp_rw [sub_mul] at htest
      rw [integral_sub hφw (hw.const_mul m), integral_const_mul] at htest
      exact sub_eq_zero.mp htest
    have hpair : (∫ t in Icc a b, φ t • (w t - c)) = 0 := by
      simp only [smul_eq_mul, mul_sub]
      rw [integral_sub hφw (hφ.continuous.integrableOn_Icc.mul_const c),
        integral_mul_const, htest']
      dsimp [m, c]
      ring
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc a b)]
    · exact hpair
    · intro t ht
      have hφt : φ t = 0 := image_eq_zero_of_notMem_tsupport
        (fun hm => ht (Ioo_subset_Icc_self (hs hm)))
      rw [hφt, zero_smul]
  have he : ∀ᵐ t ∂volume.restrict (Ioo a b), w t = c := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hz] with t ht hm
    exact sub_eq_zero.mp (ht hm)
  rwa [Measure.restrict_congr_set Ioo_ae_eq_Icc] at he

/-- Reconstruct the absolutely continuous representative from a weak L²
derivative. The additive constant is recovered, not given as an initial datum. -/
theorem HasL2TimeDerivative.exists_absolutelyContinuous_representative
    {a b : ℝ} (hab : a < b) {u du : TimeL2 ℝ a b}
    (hu : HasL2TimeDerivative a b u du) :
    ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v a b ∧
      u =ᵐ[volume.restrict (Icc a b)] v ∧
      deriv v =ᵐ[volume.restrict (Icc a b)] du := by
  have hdi : IntegrableOn (fun t => du t) (Icc a b) := (Lp.memLp du).integrable (by norm_num)
  have hdi' : IntervalIntegrable (fun t => du t) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hdi
  let p := fun t => ∫ s in a..t, du s
  have hpac : AbsolutelyContinuousOnInterval p a b :=
    hdi'.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hpc : ContinuousOn p (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using hpac.continuousOn
  have hpEq : p =ᵐ[volume.restrict (Icc a b)] timePrimitive a 0 (fun t => du t) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp [p, timePrimitive, intervalIntegral.integral_of_le ht.1, integral_Icc_eq_integral_Ioc]
  let w := fun t => u t - p t
  have hwi : IntegrableOn w (Icc a b) :=
    ((Lp.memLp u).integrable (by norm_num)).sub hpc.integrableOn_Icc
  have hw : w =ᵐ[volume.restrict (Icc a b)]
      fun _ => (∫ t in Icc a b, w t) / (b - a) := by
    apply ae_eq_mean_of_weak_derivative_zero hab hwi
    intro η η' hη hη' hηa hηb
    have huη := hu η η' hη hη' hηa hηb
    have hpη := timePrimitive_integrated hab.le (0 : ℝ) hdi η η' hη hη' hηb
    have hpη' : (∫ t in Icc a b, η' t * p t) + (∫ t in Icc a b, η t * du t) = 0 := by
      simpa only [smul_eq_mul, mul_zero] using
        ((congrArg (fun z => z + ∫ t in Icc a b, η t • du t)
          (integral_congr_ae (hpEq.mono fun t ht => congrArg (fun z => η' t • z) ht))).trans hpη)
    change (∫ t in Icc a b, η' t * (u t - p t)) = 0
    simp_rw [mul_sub]
    have hiu : Integrable (fun t => η' t * u t) (volume.restrict (Icc a b)) :=
      timeL2_weighted_integrable u η' hη'
    have hip : Integrable (fun t => η' t * p t) (volume.restrict (Icc a b)) :=
      hpc.integrableOn_Icc.continuousOn_mul hη'.continuousOn isCompact_Icc
    rw [integral_sub hiu hip]
    simp only [smul_eq_mul] at huη
    linarith
  let c := (∫ t in Icc a b, w t) / (b - a)
  refine ⟨fun t => c + p t, ?_, ?_, ?_⟩
  · apply absolutelyContinuousOnInterval_of_dist_le hpac
    intro x _hx y _hy
    simp only [dist_add_left]
    exact le_rfl
  · filter_upwards [hw] with t ht
    change u t - p t = c at ht
    linarith
  · filter_upwards [ae_restrict_of_ae hdi'.ae_hasDerivAt_integral,
      ae_restrict_mem measurableSet_Icc] with t ht hmem
    have hp := ht (by simpa only [uIcc_of_le hab.le] using hmem) a left_mem_uIcc
    exact (hp.const_add c).deriv

/-- Mean Poincaré directly from a weak L² derivative, with the geometric
constant derived from the interval. No representative or inequality is assumed. -/
theorem HasL2TimeDerivative.mean_poincare
    {a b : ℝ} (hab : a < b) {u du : TimeL2 ℝ a b}
    (hu : HasL2TimeDerivative a b u du) :
    (∫ x in Icc a b, (u x - (∫ y in Icc a b, u y) / (b - a)) ^ 2) ≤
      (b - a) ^ 2 * ∫ x in Icc a b, du x ^ 2 := by
  obtain ⟨v, hv, huv, hdv⟩ := hu.exists_absolutelyContinuous_representative hab
  have hvd : MemLp (deriv v) 2 (volume.restrict (Icc a b)) :=
    (memLp_congr_ae hdv).mpr (Lp.memLp du)
  have h := interval_mean_poincare hab hv hvd
  have hint : (∫ y in Icc a b, u y) = ∫ y in Icc a b, v y := integral_congr_ae huv
  have hleft : (∫ x in Icc a b, (u x - (∫ y in Icc a b, u y) / (b - a)) ^ 2) =
      ∫ x in Icc a b, (v x - (∫ y in Icc a b, v y) / (b - a)) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [huv] with x hx
    rw [hx, hint]
  have hright : (∫ x in Icc a b, deriv v x ^ 2) = ∫ x in Icc a b, du x ^ 2 :=
    integral_congr_ae (hdv.mono fun _ hx => congrArg (fun z : ℝ => z ^ 2) hx)
  rwa [hleft, ← hright]

end PDE
