import PDE.SobolevCompactness
import PDE.CountableTesting
import PDE.ProductMeanPoincare
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Spatial distributional identities on a cylinder give genuine weak partials
on almost every time slice. A separable L² test graph exchanges the test and
a.e.-time quantifiers; the smooth test class itself is not countable. -/

open MeasureTheory Set InnerProductSpace
open scoped ContDiff ENNReal

namespace PDE

private abbrev SpatialTest {n : ℕ} (Ω : Set (Space n)) :=
  {φ : Space n → ℝ // IsTestFunctionOn Ω φ}

private noncomputable def spatialTestGraph {n : ℕ} {Ω : Set (Space n)}
    (i : Fin n) (φ : SpatialTest Ω) : DomainL2 Ω × DomainL2 Ω :=
  ((φ.property.contDiff.continuous.memLp_of_hasCompactSupport
      φ.property.hasCompactSupport).toLp φ.val,
    ((φ.property.coordDeriv_continuous i).memLp_of_hasCompactSupport
      (φ.property.coordDeriv_hasCompactSupport i)).toLp (coordDeriv i φ.val))

private noncomputable def spatialSliceResidual {n : ℕ} (Ω : Set (Space n))
    (u du : Space n → ℝ) : (DomainL2 Ω × DomainL2 Ω) →L[ℝ] ℝ := by
  classical
  exact if h : MemLp u 2 (volume.restrict Ω) ∧ MemLp du 2 (volume.restrict Ω) then
    (innerSL ℝ (h.1.toLp u)).comp (ContinuousLinearMap.snd ℝ _ _) +
      (innerSL ℝ (h.2.toLp du)).comp (ContinuousLinearMap.fst ℝ _ _)
  else 0

private theorem spatialSliceResidual_test {n : ℕ} {Ω : Set (Space n)}
    {u du : Space n → ℝ} (hu : MemLp u 2 (volume.restrict Ω))
    (hd : MemLp du 2 (volume.restrict Ω)) (i : Fin n) (φ : SpatialTest Ω) :
    spatialSliceResidual Ω u du (spatialTestGraph i φ) =
      (∫ x in Ω, u x * coordDeriv i φ.val x) + ∫ x in Ω, du x * φ.val x := by
  rw [spatialSliceResidual, dite_eq_left ⟨hu, hd⟩]
  change inner ℝ (hu.toLp u) (spatialTestGraph i φ).2 +
    inner ℝ (hd.toLp du) (spatialTestGraph i φ).1 = _
  rw [L2.inner_def, L2.inner_def]
  congr 1
  · apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp,
      ((φ.property.coordDeriv_continuous i).memLp_of_hasCompactSupport
        (φ.property.coordDeriv_hasCompactSupport i) :
        MemLp (coordDeriv i φ.val) 2 (volume.restrict Ω)).coeFn_toLp] with x hx hy
    simp [spatialTestGraph, hx, hy, mul_comm]
  · apply integral_congr_ae
    filter_upwards [hd.coeFn_toLp,
      (φ.property.contDiff.continuous.memLp_of_hasCompactSupport
        φ.property.hasCompactSupport : MemLp φ.val 2 (volume.restrict Ω)).coeFn_toLp]
      with x hx hy
    simp [spatialTestGraph, hx, hy, mul_comm]

/-- All spatial tests hold on one common full-measure set of parameters. -/
theorem ae_hasWeakPartialOn_of_test_identities
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {n : ℕ} {Ω : Set (Space n)} {i : Fin n} {u du : α → Space n → ℝ}
    (hs : ∀ᵐ t ∂μ, MemLp (u t) 2 (volume.restrict Ω) ∧
      MemLp (du t) 2 (volume.restrict Ω))
    (htest : ∀ φ : Space n → ℝ, IsTestFunctionOn Ω φ →
      ∀ᵐ t ∂μ, (∫ x in Ω, u t x * coordDeriv i φ x) = -(∫ x in Ω, du t x * φ x)) :
    ∀ᵐ t ∂μ, HasWeakPartialOn Ω i (u t) (du t) := by
  have hz : ∀ φ : SpatialTest Ω, ∀ᵐ t ∂μ,
      spatialSliceResidual Ω (u t) (du t) (spatialTestGraph i φ) = 0 := by
    intro φ
    filter_upwards [hs, htest φ.val φ.property] with t ht hp
    rw [spatialSliceResidual_test ht.1 ht.2 i φ, hp, neg_add_cancel]
  have hall := ae_forall_continuous_tests (spatialTestGraph (Ω := Ω) i)
    (fun t => spatialSliceResidual Ω (u t) (du t))
    (Filter.Eventually.of_forall fun t => (spatialSliceResidual Ω (u t) (du t)).continuous) hz
  filter_upwards [hs, hall] with t ht htall
  refine ⟨locallyIntegrableOn_of_locallyIntegrable_restrict
    (ht.1.locallyIntegrable (by norm_num)),
    locallyIntegrableOn_of_locallyIntegrable_restrict (ht.2.locallyIntegrable (by norm_num)), ?_⟩
  intro φ hφ
  have h := htall ⟨φ, hφ⟩
  rw [spatialSliceResidual_test ht.1 ht.2] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Separated smooth time/space tests imply the spatial weak derivative on
almost every time slice, without any time derivative hypothesis. -/
theorem ae_hasWeakPartialOn_of_product_tests
    {n : ℕ} {a b : ℝ} {Ω : Set (Space n)} [IsFiniteMeasure (volume.restrict Ω)]
    {i : Fin n} {u du : ℝ × Space n → ℝ}
    (hu : MemLp u 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hd : MemLp du 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      ∀ ψ : Space n → ℝ, IsTestFunctionOn Ω ψ →
        (∫ z, φ z.1 * (u z * coordDeriv i ψ z.2 + du z * ψ z.2)
          ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) = 0) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      HasWeakPartialOn Ω i (fun x => u (t, x)) (fun x => du (t, x)) := by
  apply ae_hasWeakPartialOn_of_test_identities
    ((memLp_two_slice_right_ae hu).and (memLp_two_slice_right_ae hd))
  intro ψ hψ
  let r := fun z : ℝ × Space n => u z * coordDeriv i ψ z.2 + du z * ψ z.2
  let g := fun t : ℝ => ∫ x in Ω, r (t, x)
  have hψ2 : MemLp ψ 2 (volume.restrict Ω) :=
    hψ.contDiff.continuous.memLp_of_hasCompactSupport hψ.hasCompactSupport
  have hdψ2 : MemLp (coordDeriv i ψ) 2 (volume.restrict Ω) :=
    (hψ.coordDeriv_continuous i).memLp_of_hasCompactSupport (hψ.coordDeriv_hasCompactSupport i)
  have hr1 := hu.integrable_mul (hdψ2.comp_snd (volume.restrict (Icc a b)))
  have hr2 := hd.integrable_mul (hψ2.comp_snd (volume.restrict (Icc a b)))
  have hr : Integrable r ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) := hr1.add hr2
  have hg : IntegrableOn g (Icc a b) := hr.integral_prod_left
  have hz : ∀ᵐ t ∂volume, t ∈ Ioo a b → g t = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hg.mono_set Ioo_subset_Icc_self).locallyIntegrableOn)
    intro φ hφ hc hs
    obtain ⟨K, hK⟩ := hc.exists_bound_of_continuous hφ.continuous
    have hi : Integrable (fun z : ℝ × Space n => φ z.1 * r z)
        ((volume.restrict (Icc a b)).prod (volume.restrict Ω)) :=
      hr.bdd_mul hφ.continuous.aestronglyMeasurable.comp_fst
        (Filter.Eventually.of_forall fun z => hK z.1)
    have hp : (∫ t in Icc a b, φ t * g t) = 0 := by
      calc
        _ = ∫ t in Icc a b, ∫ x in Ω, φ t * r (t, x) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun t => (integral_const_mul _ _).symm
        _ = ∫ z, φ z.1 * r z ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω) :=
          (integral_prod _ hi).symm
        _ = 0 := hw φ hφ hc hs ψ hψ
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc a b)]
    · exact hp
    · intro t ht
      rw [image_eq_zero_of_notMem_tsupport (fun h => ht (Ioo_subset_Icc_self (hs h))), zero_smul]
  have hgz : ∀ᵐ t ∂volume.restrict (Icc a b), g t = 0 := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc, ae_restrict_iff' measurableSet_Ioo]
    exact hz
  filter_upwards [hgz, hr1.prod_right_ae, hr2.prod_right_ae] with t ht hi1 hi2
  change (∫ x in Ω, u (t, x) * coordDeriv i ψ x + du (t, x) * ψ x) = 0 at ht
  change Integrable (fun x => u (t, x) * coordDeriv i ψ x) (volume.restrict Ω) at hi1
  change Integrable (fun x => du (t, x) * ψ x) (volume.restrict Ω) at hi2
  rw [integral_add hi1 hi2] at ht
  exact eq_neg_of_add_eq_zero_left ht

end PDE
