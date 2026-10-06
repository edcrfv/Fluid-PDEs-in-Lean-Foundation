import PDE.IntervalTestFunctions

/-!
# Reconstructing functions from compact-test weak differentiation

The weak identity here uses only smooth tests compactly supported in the open
interval, as in distributional Sobolev spaces. The endpoints have zero measure.
Both the function and its derivative are actual integrable functions. The
representative is constructed; neither absolute continuity nor boundary traces
are assumed. The reconstruction also works for Banach-valued functions.
-/

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Distributional differentiation on a finite interval, using precisely
compactly supported smooth tests. Integrability includes the whole interval. -/
structure HasWeakDerivativeOnInterval (a b : ℝ) (u du : ℝ → E) : Prop where
  integrable : IntegrableOn u (Icc a b)
  derivative_integrable : IntegrableOn du (Icc a b)
  integration_by_parts : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ Ioo a b →
      (∫ t in Icc a b, deriv φ t • u t) = -(∫ t in Icc a b, φ t • du t)

omit [CompleteSpace E] in
/-- Distributional differentiation is a relation of a.e. classes. In particular,
it does not force the supplied pointwise representative to be continuous. -/
theorem HasWeakDerivativeOnInterval.congr {a b : ℝ} {u du v dv : ℝ → E}
    (hu : HasWeakDerivativeOnInterval a b u du)
    (huv : u =ᵐ[volume.restrict (Icc a b)] v)
    (hdv : du =ᵐ[volume.restrict (Icc a b)] dv) :
    HasWeakDerivativeOnInterval a b v dv := by
  refine ⟨hu.integrable.congr huv, hu.derivative_integrable.congr hdv, ?_⟩
  intro φ hφ hc hs
  calc
    _ = ∫ t in Icc a b, deriv φ t • u t :=
      integral_congr_ae (huv.symm.mono fun t ht => congrArg (fun z => deriv φ t • z) ht)
    _ = -(∫ t in Icc a b, φ t • du t) := hu.integration_by_parts φ hφ hc hs
    _ = _ := congrArg Neg.neg
      (integral_congr_ae (hdv.mono fun t ht => congrArg (fun z => φ t • z) ht))

/-- A zero distributional derivative forces an integrable function to be a.e.
constant. The proof constructs compact primitive tests, not extra endpoint tests. -/
theorem exists_ae_eq_const_of_compact_weak_derivative_zero
    {a b : ℝ} (hab : a < b) {w : ℝ → E} (hw : IntegrableOn w (Icc a b))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ t in Icc a b, deriv φ t • w t) = 0) :
    ∃ c : E, w =ᵐ[volume.restrict (Icc a b)] fun _ => c := by
  obtain ⟨ψ, hψ, hcψ, hsψ, hiψ⟩ := exists_normalized_interval_test hab
  let c : E := ∫ t in Icc a b, ψ t • w t
  have hdiff : IntegrableOn (fun t => w t - c) (Icc a b) := hw.sub (integrable_const c)
  have hz : ∀ᵐ t ∂volume, t ∈ Ioo a b → w t - c = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hdiff.mono_set Ioo_subset_Icc_self).locallyIntegrableOn)
    intro φ hφ hcφ hsφ
    let m : ℝ := ∫ t, φ t
    let χ := fun t => φ t - m * ψ t
    have hχ : ContDiff ℝ ∞ χ := hφ.sub (contDiff_const.mul hψ)
    have hcχ : HasCompactSupport χ := hcφ.sub (hcψ.mul_left (f := fun _ => m))
    have hsχ : tsupport χ ⊆ Ioo a b :=
      (tsupport_sub φ (fun t => m * ψ t)).trans
        (union_subset hsφ (tsupport_mul_subset_right.trans hsψ))
    have hizero : (∫ t, χ t) = 0 := by
      rw [integral_sub (hφ.continuous.integrable_of_hasCompactSupport hcφ)
        ((hψ.continuous.integrable_of_hasCompactSupport hcψ).const_mul m),
        integral_const_mul, hiψ, mul_one]
      exact sub_self m
    obtain ⟨η, hη, hcη, hsη, hdη⟩ :=
      exists_compact_primitive_on_interval hab hχ hcχ hsχ hizero
    have ht := hweak η hη hcη hsη
    have hder : deriv η = χ := funext fun t => (hdη t).deriv
    rw [hder] at ht
    have hφw : IntegrableOn (fun t => φ t • w t) (Icc a b) :=
      hw.continuousOn_smul hφ.continuous.continuousOn isCompact_Icc
    have hψw : IntegrableOn (fun t => ψ t • w t) (Icc a b) :=
      hw.continuousOn_smul hψ.continuous.continuousOn isCompact_Icc
    have hφmean : (∫ t in Icc a b, φ t • w t) = m • c := by
      change (∫ t in Icc a b, (φ t - m * ψ t) • w t) = 0 at ht
      simp_rw [sub_smul, mul_smul] at ht
      have hmψw : Integrable (fun t => m • (ψ t • w t)) (volume.restrict (Icc a b)) :=
        hψw.smul m
      rw [integral_sub hφw hmψw, integral_smul] at ht
      exact sub_eq_zero.mp ht
    have hφint : (∫ t in Icc a b, φ t) = m :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht =>
        image_eq_zero_of_notMem_tsupport (fun hm => ht (Ioo_subset_Icc_self (hsφ hm))))
    have hpair : (∫ t in Icc a b, φ t • (w t - c)) = 0 := by
      simp_rw [smul_sub]
      rw [integral_sub hφw (hφ.continuous.integrableOn_Icc.smul_const c),
        integral_smul_const, hφmean, hφint, sub_self]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc a b)]
    · exact hpair
    · intro t ht
      rw [image_eq_zero_of_notMem_tsupport (fun hm => ht (Ioo_subset_Icc_self (hsφ hm))),
        zero_smul]
  refine ⟨c, ?_⟩
  have he : ∀ᵐ t ∂volume.restrict (Ioo a b), w t = c := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hz] with t ht hm
    exact sub_eq_zero.mp (ht hm)
  rwa [Measure.restrict_congr_set Ioo_ae_eq_Icc] at he

/-- Distributional differentiation reconstructs an integral representative.
The additive constant is a conclusion, not a prescribed trace. -/
theorem HasWeakDerivativeOnInterval.exists_integral_representative
    {a b : ℝ} (hab : a < b) {u du : ℝ → E}
    (hu : HasWeakDerivativeOnInterval a b u du) :
    ∃ c : E, u =ᵐ[volume.restrict (Icc a b)] fun t => c + ∫ s in a..t, du s := by
  let p := fun t => ∫ s in a..t, du s
  have hdi : IntervalIntegrable du volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hu.derivative_integrable
  have hpac : AbsolutelyContinuousOnInterval p a b := intervalIntegral_absolutelyContinuous hdi
  have hpc : ContinuousOn p (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using hpac.continuousOn
  have hpEq : p =ᵐ[volume.restrict (Icc a b)] timePrimitive a 0 du := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp [p, timePrimitive, intervalIntegral.integral_of_le ht.1, integral_Icc_eq_integral_Ioc]
  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_compact_weak_derivative_zero hab
    (hu.integrable.sub hpc.integrableOn_Icc) (by
      intro φ hφ _hcφ hsφ
      have hdφ : ∀ t, HasDerivAt φ (deriv φ t) t := fun t =>
        (hφ.differentiable (by simp)).differentiableAt.hasDerivAt
      have hφb : φ b = 0 := image_eq_zero_of_notMem_tsupport (fun ht => (hsφ ht).2.false)
      have hpφ := timePrimitive_integrated hab.le (0 : E) hu.derivative_integrable
        φ (deriv φ) hdφ (hφ.continuous_deriv (by simp)) hφb
      have hpφ' : (∫ t in Icc a b, deriv φ t • p t) +
          (∫ t in Icc a b, φ t • du t) = 0 := by
        simpa only [smul_zero] using
          ((congrArg (fun z => z + ∫ t in Icc a b, φ t • du t)
            (integral_congr_ae (hpEq.mono fun t ht => congrArg (fun z => deriv φ t • z) ht))).trans hpφ)
      have hdφc := hφ.continuous_deriv (by simp)
      have hiu : Integrable (fun t => deriv φ t • u t) (volume.restrict (Icc a b)) :=
        hu.integrable.continuousOn_smul hdφc.continuousOn isCompact_Icc
      have hip : Integrable (fun t => deriv φ t • p t) (volume.restrict (Icc a b)) :=
        hpc.integrableOn_Icc.continuousOn_smul hdφc.continuousOn isCompact_Icc
      change (∫ t in Icc a b, deriv φ t • (u t - p t)) = 0
      simp_rw [smul_sub]
      rw [integral_sub hiu hip, hu.integration_by_parts φ hφ _hcφ hsφ,
        eq_neg_of_add_eq_zero_left hpφ', sub_self])
  refine ⟨c, hc.mono fun t ht => ?_⟩
  change u t - p t = c at ht
  exact sub_eq_iff_eq_add.mp ht

/-- Compact-test weak differentiation supplies an absolutely continuous
representative with the given derivative a.e., including in Banach spaces. -/
theorem HasWeakDerivativeOnInterval.exists_absolutelyContinuous_representative
    {a b : ℝ} (hab : a < b) {u du : ℝ → E}
    (hu : HasWeakDerivativeOnInterval a b u du) :
    ∃ v : ℝ → E, AbsolutelyContinuousOnInterval v a b ∧
      u =ᵐ[volume.restrict (Icc a b)] v ∧ deriv v =ᵐ[volume.restrict (Icc a b)] du := by
  obtain ⟨c, hc⟩ := hu.exists_integral_representative hab
  have hdi : IntervalIntegrable du volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hu.derivative_integrable
  refine ⟨fun t => c + ∫ s in a..t, du s, ?_, hc, ?_⟩
  · apply absolutelyContinuousOnInterval_of_dist_le (intervalIntegral_absolutelyContinuous hdi)
    intro x _hx y _hy
    simp only [dist_add_left]
    exact le_rfl
  · filter_upwards [ae_restrict_of_ae hdi.ae_hasDerivAt_integral,
      ae_restrict_mem measurableSet_Icc] with t ht hmem
    have hp := ht (by simpa only [uIcc_of_le hab.le] using hmem) a left_mem_uIcc
    exact (hp.const_add c).deriv

/-- Compact smooth distributional tests imply the C¹ zero-endpoint identity
used by `HasL2TimeDerivative`; this is proved through the integral representative. -/
theorem HasWeakDerivativeOnInterval.integration_by_parts_C1
    {a b : ℝ} (hab : a < b) {u du : ℝ → E}
    (hu : HasWeakDerivativeOnInterval a b u du)
    (η η' : ℝ → ℝ) (hη : ∀ t, HasDerivAt η (η' t) t) (hη' : Continuous η')
    (hηa : η a = 0) (hηb : η b = 0) :
    (∫ t in Icc a b, η' t • u t) = -(∫ t in Icc a b, η t • du t) := by
  obtain ⟨c, hc⟩ := hu.exists_integral_representative hab
  have hrep : u =ᵐ[volume.restrict (Icc a b)] timePrimitive a c du := by
    filter_upwards [hc, ae_restrict_mem measurableSet_Icc] with t ht hmem
    simpa [timePrimitive, intervalIntegral.integral_of_le hmem.1, integral_Icc_eq_integral_Ioc]
      using ht
  have hp := timePrimitive_integrated hab.le c hu.derivative_integrable η η' hη hη' hηb
  rw [hηa, neg_zero, zero_smul] at hp
  rw [integral_congr_ae (hrep.mono fun t ht => congrArg (fun z => η' t • z) ht)]
  exact eq_neg_of_add_eq_zero_left hp

/-- Mean Poincaré from compact smooth weak differentiation; absolute continuity
of the representative and the interval constant are both derived. -/
theorem HasWeakDerivativeOnInterval.mean_poincare
    {a b : ℝ} (hab : a < b) {u du : ℝ → ℝ}
    (hu : HasWeakDerivativeOnInterval a b u du)
    (hu2 : MemLp u 2 (volume.restrict (Icc a b)))
    (hd2 : MemLp du 2 (volume.restrict (Icc a b))) :
    (∫ x in Icc a b, (u x - (∫ y in Icc a b, u y) / (b - a)) ^ 2) ≤
      (b - a) ^ 2 * ∫ x in Icc a b, du x ^ 2 := by
  have hw : HasL2TimeDerivative a b (hu2.toLp u) (hd2.toLp du) := by
    intro η η' hη hη' hηa hηb
    rw [integral_congr_ae (hu2.coeFn_toLp.mono fun t ht => congrArg (fun z => η' t • z) ht),
      integral_congr_ae (hd2.coeFn_toLp.mono fun t ht => congrArg (fun z => η t • z) ht)]
    exact hu.integration_by_parts_C1 hab η η' hη hη' hηa hηb
  have h := hw.mean_poincare hab
  have hi := integral_congr_ae hu2.coeFn_toLp
  have hl := integral_congr_ae (hu2.coeFn_toLp.mono fun t ht => by
    show ((hu2.toLp u) t - (∫ y in Icc a b, (hu2.toLp u) y) / (b - a)) ^ 2 =
      (u t - (∫ y in Icc a b, u y) / (b - a)) ^ 2
    rw [ht, hi])
  have hr := integral_congr_ae (hd2.coeFn_toLp.mono fun _ ht => congrArg (fun z : ℝ => z ^ 2) ht)
  rwa [hl, hr] at h

end PDE
