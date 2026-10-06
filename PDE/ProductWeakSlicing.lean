import PDE.IntervalWeakSlicing
import PDE.ProductMeanPoincare
import PDE.WeakDerivativeOn

/-!
# Distributional product tests give weak differentiation on almost every line

Fubini and smooth-test separation first give an identity a.e. for each interval
test. The countable L² test-graph argument then gives one full-measure set on
which all tests hold. The input is a genuine integration-by-parts identity for
product tests, not assumed regularity of line restrictions.
-/

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace PDE

/-- A distributional identity for all compact product tests implies genuine
weak interval differentiation on almost every transverse slice. -/
theorem ae_hasWeakDerivativeOnInterval_of_product_tests
    {n : ℕ} {a b : ℝ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    [IsFiniteMeasure (volume.restrict Ω)] {u du : ℝ × Space n → ℝ}
    (hu : MemLp u 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hd : MemLp du 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      ∀ ψ : Space n → ℝ, IsTestFunctionOn Ω ψ →
        (∫ z, ψ z.2 * (deriv φ z.1 * u z + φ z.1 * du z)
          ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) = 0) :
    ∀ᵐ x ∂volume.restrict Ω,
      HasWeakDerivativeOnInterval a b (fun t => u (t, x)) (fun t => du (t, x)) := by
  have hslices : ∀ᵐ x ∂volume.restrict Ω,
      MemLp (fun t => u (t, x)) 2 (volume.restrict (Icc a b)) ∧
      MemLp (fun t => du (t, x)) 2 (volume.restrict (Icc a b)) := by
    filter_upwards [hu.aestronglyMeasurable.prodMk_right, hu.integrable_sq.prod_left_ae,
      hd.aestronglyMeasurable.prodMk_right, hd.integrable_sq.prod_left_ae] with x hum hui hdm hdi
    exact ⟨(memLp_two_iff_integrable_sq hum).mpr hui, (memLp_two_iff_integrable_sq hdm).mpr hdi⟩
  apply ae_hasWeakDerivativeOnInterval_of_test_identities hslices
  intro φ hφ hcφ hsφ
  let r := fun z : ℝ × Space n => deriv φ z.1 * u z + φ z.1 * du z
  let g := fun x : Space n => ∫ t in Icc a b, r (t, x)
  have hφ2 : MemLp φ 2 (volume.restrict (Icc a b)) :=
    hφ.continuous.memLp_of_hasCompactSupport hcφ
  have hdφ2 : MemLp (deriv φ) 2 (volume.restrict (Icc a b)) :=
    (hφ.continuous_deriv (by simp)).memLp_of_hasCompactSupport hcφ.deriv
  have hr1 : Integrable (fun z => deriv φ z.1 * u z)
      ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) :=
    (hdφ2.comp_fst (volume.restrict Ω)).integrable_mul hu
  have hr2 : Integrable (fun z => φ z.1 * du z)
      ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) :=
    (hφ2.comp_fst (volume.restrict Ω)).integrable_mul hd
  have hr : Integrable r ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) := hr1.add hr2
  have hg : IntegrableOn g Ω := hr.integral_prod_right
  have hz : ∀ᵐ x ∂volume, x ∈ Ω → g x = 0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hg.locallyIntegrableOn
    intro ψ hψ hcψ hsψ
    obtain ⟨C, hC⟩ := hcψ.exists_bound_of_continuous hψ.continuous
    have hψr : Integrable (fun z : ℝ × Space n => ψ z.2 * r z)
        ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) :=
      hr.bdd_mul hψ.continuous.aestronglyMeasurable.comp_snd
        (Filter.Eventually.of_forall fun z => hC z.2)
    have hpair : (∫ x in Ω, ψ x * g x) = 0 := by
      calc
        _ = ∫ x in Ω, ∫ t in Icc a b, ψ x * r (t, x) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => (integral_const_mul _ _).symm
        _ = ∫ z, ψ z.2 * r z ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω) :=
          (integral_prod_symm _ hψr).symm
        _ = 0 := hweak φ hφ hcφ hsφ ψ ⟨hψ, hcψ, hsψ⟩
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω)]
    · exact hpair
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsψ ht)), zero_smul]
  have hgz : ∀ᵐ x ∂volume.restrict Ω, g x = 0 := by
    rw [ae_restrict_iff' hΩ.measurableSet]
    exact hz
  filter_upwards [hgz, hr1.prod_left_ae, hr2.prod_left_ae] with x hx hi1 hi2
  change (∫ t in Icc a b, deriv φ t * u (t, x) + φ t * du (t, x)) = 0 at hx
  rw [integral_add hi1 hi2] at hx
  exact eq_neg_of_add_eq_zero_left hx

/-- Genuine product weak differentiation gives almost-everywhere AC line
representatives with the specified derivative, without a supplied trace. -/
theorem ae_exists_interval_AC_representative_of_product_tests
    {n : ℕ} {a b : ℝ} (hab : a < b) {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    [IsFiniteMeasure (volume.restrict Ω)] {u du : ℝ × Space n → ℝ}
    (hu : MemLp u 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hd : MemLp du 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      ∀ ψ : Space n → ℝ, IsTestFunctionOn Ω ψ →
        (∫ z, ψ z.2 * (deriv φ z.1 * u z + φ z.1 * du z)
          ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) = 0) :
    ∀ᵐ x ∂volume.restrict Ω, ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v a b ∧
      (fun t => u (t, x)) =ᵐ[volume.restrict (Icc a b)] v ∧
      deriv v =ᵐ[volume.restrict (Icc a b)] (fun t => du (t, x)) :=
  (ae_hasWeakDerivativeOnInterval_of_product_tests hΩ hu hd hweak).mono
    fun _ hx => hx.exists_absolutelyContinuous_representative hab

end PDE
