import PDE.ClassicalWeakDerivative
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Distributional heat solutions on open space–time domains

Coordinate zero is time and the remaining coordinates are spatial. The solution
predicate uses locally integrable representatives and the actual distributional
test identity. No smoothness of a weak solution is assumed or concluded here.
-/

open MeasureTheory Set
open scoped ContDiff BigOperators

namespace PDE

def heatCylinder {n : ℕ} (Ω : Set (Space n)) (T : ℝ) : Set (Space (n + 1)) :=
  {z | z 0 ∈ Ioo 0 T ∧ (fun i : Fin n => z i.succ) ∈ Ω}

theorem isOpen_heatCylinder {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω) (T : ℝ) :
    IsOpen (heatCylinder Ω T) :=
  (isOpen_Ioo.preimage (continuous_apply 0)).inter
    (hΩ.preimage (continuous_pi fun i => continuous_apply i.succ))

noncomputable def spaceTimeLaplacian {n : ℕ} (f : Space (n + 1) → ℝ)
    (z : Space (n + 1)) : ℝ :=
  ∑ i : Fin n, coordDeriv i.succ (coordDeriv i.succ f) z

/-- The test operator for the homogeneous heat equation, with the sign from
distributional time differentiation absorbed into the zero right hand side. -/
noncomputable def heatAdjointTest {n : ℕ} (φ : Space (n + 1) → ℝ)
    (z : Space (n + 1)) : ℝ :=
  coordDeriv 0 φ z + spaceTimeLaplacian φ z

/-- The classical residual of the heat equation. -/
noncomputable def heatResidual {n : ℕ} (u : Space (n + 1) → ℝ)
    (z : Space (n + 1)) : ℝ :=
  coordDeriv 0 u z - spaceTimeLaplacian u z

theorem IsTestFunctionOn.coordDeriv {d : ℕ} {Q : Set (Space d)}
    {φ : Space d → ℝ} (hφ : IsTestFunctionOn Q φ) (i : Fin d) :
    IsTestFunctionOn Q (coordDeriv i φ) :=
  ⟨(hφ.contDiff.fderiv_right (by simp)).clm_apply contDiff_const,
    hφ.coordDeriv_hasCompactSupport i, hφ.coordDeriv_tsupport_subset i⟩

private theorem testFunction_sum {d : ℕ} {Q : Set (Space d)} {ι : Type*}
    (s : Finset ι) (f : ι → Space d → ℝ)
    (hf : ∀ i ∈ s, IsTestFunctionOn Q (f i)) :
    IsTestFunctionOn Q (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    convert IsTestFunctionOn.zero Q using 1
    ext z
    simp
  | @insert a s ha ih =>
    convert
      (hf a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))) using 1
    ext z
    simp only [Finset.sum_insert ha, Pi.add_apply]

theorem IsTestFunctionOn.spaceTimeLaplacian {n : ℕ} {Q : Set (Space (n + 1))}
    {φ : Space (n + 1) → ℝ} (hφ : IsTestFunctionOn Q φ) :
    IsTestFunctionOn Q (spaceTimeLaplacian φ) :=
  testFunction_sum Finset.univ _ (fun i _ => (hφ.coordDeriv i.succ).coordDeriv i.succ)

theorem IsTestFunctionOn.heatAdjointTest {n : ℕ} {Q : Set (Space (n + 1))}
    {φ : Space (n + 1) → ℝ} (hφ : IsTestFunctionOn Q φ) :
    IsTestFunctionOn Q (heatAdjointTest φ) :=
  (hφ.coordDeriv 0).add hφ.spaceTimeLaplacian

/-- Distributional heat equation on a space–time set. Openness is required by
the regularity and classical-equivalence results, not by this predicate. -/
structure IsDistributionalHeatSolution {n : ℕ} (Q : Set (Space (n + 1)))
    (u : Space (n + 1) → ℝ) : Prop where
  locallyIntegrable : LocallyIntegrableOn u Q volume
  equation : ∀ φ : Space (n + 1) → ℝ, IsTestFunctionOn Q φ →
    (∫ z in Q, u z * heatAdjointTest φ z) = 0

namespace IsDistributionalHeatSolution

variable {n : ℕ} {Q Q' : Set (Space (n + 1))} {u v : Space (n + 1) → ℝ}

theorem integrable_pairing (hu : IsDistributionalHeatSolution Q u)
    {φ : Space (n + 1) → ℝ} (hφ : IsTestFunctionOn Q φ) :
    Integrable (fun z => u z * heatAdjointTest φ z) volume :=
  integrable_mul_of_locallyIntegrableOn hu.locallyIntegrable
    hφ.heatAdjointTest.contDiff.continuous hφ.heatAdjointTest.hasCompactSupport
    hφ.heatAdjointTest.tsupport_subset

theorem equation_global (hu : IsDistributionalHeatSolution Q u)
    {φ : Space (n + 1) → ℝ} (hφ : IsTestFunctionOn Q φ) :
    (∫ z, u z * heatAdjointTest φ z) = 0 := by
  rw [← setIntegral_mul_eq_integral_of_tsupport_subset _ _
    hφ.heatAdjointTest.tsupport_subset]
  exact hu.equation φ hφ

theorem congr (hu : IsDistributionalHeatSolution Q u)
    (huv : u =ᵐ[volume.restrict Q] v) : IsDistributionalHeatSolution Q v := by
  refine ⟨hu.locallyIntegrable.congr huv, ?_⟩
  intro φ hφ
  rw [← hu.equation φ hφ]
  exact integral_congr_ae (huv.symm.mono fun z hz => congrArg (· * heatAdjointTest φ z) hz)

theorem mono (hu : IsDistributionalHeatSolution Q u) (hQ : Q' ⊆ Q) :
    IsDistributionalHeatSolution Q' u := by
  refine ⟨hu.locallyIntegrable.mono_set hQ, ?_⟩
  intro φ hφ
  rw [setIntegral_mul_eq_integral_of_tsupport_subset _ _ hφ.heatAdjointTest.tsupport_subset]
  exact hu.equation_global (hφ.mono hQ)

theorem zero (Q : Set (Space (n + 1))) :
    IsDistributionalHeatSolution Q (fun _ => 0) := by
  refine ⟨locallyIntegrableOn_zero, ?_⟩
  intro φ _
  simp

theorem add (hu : IsDistributionalHeatSolution Q u)
    (hv : IsDistributionalHeatSolution Q v) :
    IsDistributionalHeatSolution Q (u + v) := by
  refine ⟨hu.locallyIntegrable.add hv.locallyIntegrable, ?_⟩
  intro φ hφ
  simp only [Pi.add_apply, add_mul]
  rw [integral_add (hu.integrable_pairing hφ).integrableOn
    (hv.integrable_pairing hφ).integrableOn, hu.equation φ hφ, hv.equation φ hφ, zero_add]

theorem smul (hu : IsDistributionalHeatSolution Q u) (c : ℝ) :
    IsDistributionalHeatSolution Q (c • u) := by
  refine ⟨hu.locallyIntegrable.smul c, ?_⟩
  intro φ hφ
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul,
    hu.equation φ hφ, mul_zero]

end IsDistributionalHeatSolution

/-- Uniqueness of the continuous representative is a topological consequence of
a.e. equality on an open set; it does not require the heat equation. -/
theorem heat_continuousRepresentative_unique {n : ℕ} {Q : Set (Space (n + 1))}
    (hQ : IsOpen Q) {u v w : Space (n + 1) → ℝ}
    (hv : ContinuousOn v Q) (hw : ContinuousOn w Q)
    (huv : u =ᵐ[volume.restrict Q] v) (huw : u =ᵐ[volume.restrict Q] w) :
    EqOn v w Q :=
  MeasureTheory.Measure.eqOn_open_of_ae_eq (huv.symm.trans huw) hQ hv hw

theorem contDiffOn_coordDeriv_infty {d : ℕ} {Q : Set (Space d)} (hQ : IsOpen Q)
    {u : Space d → ℝ} (hu : ContDiffOn ℝ ∞ u Q) (i : Fin d) :
    ContDiffOn ℝ ∞ (coordDeriv i u) Q :=
  (hu.fderiv_of_isOpen hQ (by simp)).clm_apply contDiffOn_const

theorem heatResidual_continuousOn {n : ℕ} {Q : Set (Space (n + 1))}
    (hQ : IsOpen Q) {u : Space (n + 1) → ℝ} (hu : ContDiffOn ℝ ∞ u Q) :
    ContinuousOn (heatResidual u) Q := by
  apply (contDiffOn_coordDeriv_infty hQ hu 0).continuousOn.sub
  exact (ContDiffOn.sum (fun i _ => contDiffOn_coordDeriv_infty hQ
    (contDiffOn_coordDeriv_infty hQ hu i.succ) i.succ)).continuousOn

/-- Twice integrating by parts produces the positive spatial sign. -/
theorem integral_coordDeriv_twice_mul {d : ℕ} {Q : Set (Space d)}
    (hQ : IsOpen Q) {u φ : Space d → ℝ} (hu : ContDiffOn ℝ ∞ u Q)
    (hφ : IsTestFunctionOn Q φ) (i : Fin d) :
    (∫ z in Q, u z * coordDeriv i (coordDeriv i φ) z) =
      ∫ z in Q, coordDeriv i (coordDeriv i u) z * φ z := by
  have h1 := hasWeakPartialOn_of_contDiffOn hQ i (hu.of_le (by simp))
  have h2 := hasWeakPartialOn_of_contDiffOn hQ i
    ((contDiffOn_coordDeriv_infty hQ hu i).of_le (by simp))
  rw [h1.integration_by_parts _ (hφ.coordDeriv i), h2.integration_by_parts _ hφ, neg_neg]

theorem heat_laplacian_pairing {n : ℕ} {Q : Set (Space (n + 1))}
    (hQ : IsOpen Q) {u φ : Space (n + 1) → ℝ} (hu : ContDiffOn ℝ ∞ u Q)
    (hφ : IsTestFunctionOn Q φ) :
    (∫ z in Q, u z * spaceTimeLaplacian φ z) =
      ∫ z in Q, spaceTimeLaplacian u z * φ z := by
  have hlu := hu.continuousOn.locallyIntegrableOn (μ := volume) hQ.measurableSet
  have hleft (i : Fin n) :
      IntegrableOn (fun z => u z * coordDeriv i.succ (coordDeriv i.succ φ) z) Q := by
    have ht := (hφ.coordDeriv i.succ).coordDeriv i.succ
    exact (integrable_mul_of_locallyIntegrableOn hlu ht.contDiff.continuous
      ht.hasCompactSupport ht.tsupport_subset).integrableOn
  have hright (i : Fin n) :
      IntegrableOn (fun z => coordDeriv i.succ (coordDeriv i.succ u) z * φ z) Q := by
    have hd := contDiffOn_coordDeriv_infty hQ
      (contDiffOn_coordDeriv_infty hQ hu i.succ) i.succ
    exact (integrable_mul_of_locallyIntegrableOn
      (hd.continuousOn.locallyIntegrableOn hQ.measurableSet) hφ.contDiff.continuous
        hφ.hasCompactSupport hφ.tsupport_subset).integrableOn
  simp only [spaceTimeLaplacian, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => hleft i),
    integral_finsetSum _ (fun i _ => hright i)]
  exact Finset.sum_congr rfl (fun i _ => integral_coordDeriv_twice_mul hQ hu hφ i.succ)

/-- The distributional heat test is the negative pairing with the classical
residual, with both integrations by parts and all integrability justified. -/
theorem heat_pairing_eq_neg_residual {n : ℕ} {Q : Set (Space (n + 1))}
    (hQ : IsOpen Q) {u φ : Space (n + 1) → ℝ} (hu : ContDiffOn ℝ ∞ u Q)
    (hφ : IsTestFunctionOn Q φ) :
    (∫ z in Q, u z * heatAdjointTest φ z) =
      -(∫ z in Q, heatResidual u z * φ z) := by
  have hlu := hu.continuousOn.locallyIntegrableOn (μ := volume) hQ.measurableSet
  have htime := hasWeakPartialOn_of_contDiffOn hQ (0 : Fin (n + 1)) (hu.of_le (by simp))
  have hi_time := (integrable_mul_of_locallyIntegrableOn hlu
    (hφ.coordDeriv 0).contDiff.continuous (hφ.coordDeriv 0).hasCompactSupport
    (hφ.coordDeriv 0).tsupport_subset).integrableOn (s := Q)
  have hi_lap := (integrable_mul_of_locallyIntegrableOn hlu
    hφ.spaceTimeLaplacian.contDiff.continuous hφ.spaceTimeLaplacian.hasCompactSupport
    hφ.spaceTimeLaplacian.tsupport_subset).integrableOn (s := Q)
  have hi_dtime := (integrable_mul_of_locallyIntegrableOn htime.derivative_locallyIntegrable
    hφ.contDiff.continuous hφ.hasCompactSupport hφ.tsupport_subset).integrableOn (s := Q)
  have hlap : ContinuousOn (spaceTimeLaplacian u) Q :=
    (ContDiffOn.sum (fun i _ => contDiffOn_coordDeriv_infty hQ
      (contDiffOn_coordDeriv_infty hQ hu i.succ) i.succ)).continuousOn
  have hi_dlap := (integrable_mul_of_locallyIntegrableOn
    (hlap.locallyIntegrableOn hQ.measurableSet) hφ.contDiff.continuous
    hφ.hasCompactSupport hφ.tsupport_subset).integrableOn (s := Q)
  simp only [heatAdjointTest, heatResidual, mul_add, sub_mul]
  rw [integral_add hi_time hi_lap, integral_sub hi_dtime hi_dlap,
    htime.integration_by_parts φ hφ, heat_laplacian_pairing hQ hu hφ]
  ring

/-- For a smooth function, the distributional heat equation is exactly the
pointwise heat equation. This equivalence does not prove smoothness of weak solutions. -/
theorem isDistributionalHeatSolution_iff_of_contDiffOn {n : ℕ}
    {Q : Set (Space (n + 1))} (hQ : IsOpen Q) {u : Space (n + 1) → ℝ}
    (hu : ContDiffOn ℝ ∞ u Q) :
    IsDistributionalHeatSolution Q u ↔
      ∀ z ∈ Q, coordDeriv 0 u z = spaceTimeLaplacian u z := by
  constructor
  · intro h
    have hc := heatResidual_continuousOn hQ hu
    have hae : ∀ᵐ z ∂volume, z ∈ Q → heatResidual u z = 0 := by
      apply hQ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (hc.locallyIntegrableOn hQ.measurableSet)
      intro φ hφ hcompact hsupp
      have ht : IsTestFunctionOn Q φ := ⟨hφ, hcompact, hsupp⟩
      have heq := heat_pairing_eq_neg_residual hQ hu ht
      rw [h.equation φ ht] at heq
      have hz : (∫ z in Q, heatResidual u z * φ z) = 0 := by linarith
      rw [setIntegral_mul_eq_integral_of_tsupport_subset _ _ hsupp] at hz
      simpa only [smul_eq_mul, mul_comm] using hz
    have hae' : heatResidual u =ᵐ[volume.restrict Q] (fun _ => 0) :=
      (ae_restrict_iff' hQ.measurableSet).mpr hae
    have hp := MeasureTheory.Measure.eqOn_open_of_ae_eq hae' hQ hc continuousOn_const
    intro z hz
    exact sub_eq_zero.mp (hp hz)
  · intro h
    refine ⟨hu.continuousOn.locallyIntegrableOn hQ.measurableSet, ?_⟩
    intro φ hφ
    rw [heat_pairing_eq_neg_residual hQ hu hφ]
    have hz : (∫ z in Q, heatResidual u z * φ z) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro z hz
      simp only [heatResidual, h z hz, sub_self, zero_mul]
    rw [hz, neg_zero]

end PDE
