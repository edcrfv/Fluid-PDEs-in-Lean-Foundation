import PDE.WeakDerivative

/-!
# Weak first derivatives on an open domain

The definition records the actual integration-by-parts identity with restricted volume.
The compact-support integrability argument follows the approach of `IntMulLocalintComp`
in the pinned `weiran-sun/pde` reference, adapted to unbundled representatives and this API.
-/

open MeasureTheory Set
open scoped ContDiff

namespace PDE

/-- A scalar smooth test function compactly supported inside `Ω`. -/
structure IsTestFunctionOn {n : ℕ} (Ω : Set (Space n)) (φ : Space n → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ φ
  hasCompactSupport : HasCompactSupport φ
  tsupport_subset : tsupport φ ⊆ Ω

namespace IsTestFunctionOn

variable {n : ℕ} {Ω Ω' : Set (Space n)} {φ : Space n → ℝ}

theorem zero (Ω : Set (Space n)) : IsTestFunctionOn Ω 0 := by
  exact ⟨contDiff_const, by simp [HasCompactSupport], by simp⟩

theorem add {ψ : Space n → ℝ} (hφ : IsTestFunctionOn Ω φ)
    (hψ : IsTestFunctionOn Ω ψ) : IsTestFunctionOn Ω (φ + ψ) :=
  ⟨hφ.contDiff.add hψ.contDiff, hφ.hasCompactSupport.add hψ.hasCompactSupport,
    (tsupport_add φ ψ).trans (union_subset hφ.tsupport_subset hψ.tsupport_subset)⟩

theorem smul (hφ : IsTestFunctionOn Ω φ) (c : ℝ) : IsTestFunctionOn Ω (c • φ) := by
  refine ⟨contDiff_const.smul hφ.contDiff, ?_, ?_⟩
  · exact hφ.hasCompactSupport.smul_left (f := fun _ => c)
  · exact (tsupport_smul_subset_right (fun _ => c) φ).trans hφ.tsupport_subset

theorem mono (hφ : IsTestFunctionOn Ω φ) (hΩ : Ω ⊆ Ω') : IsTestFunctionOn Ω' φ :=
  ⟨hφ.contDiff, hφ.hasCompactSupport, hφ.tsupport_subset.trans hΩ⟩

theorem coordDeriv_continuous (hφ : IsTestFunctionOn Ω φ) (i : Fin n) :
    Continuous (coordDeriv i φ) :=
  (hφ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const

theorem coordDeriv_hasCompactSupport (hφ : IsTestFunctionOn Ω φ) (i : Fin n) :
    HasCompactSupport (coordDeriv i φ) :=
  hφ.hasCompactSupport.fderiv_apply ℝ (Pi.single i 1)

theorem coordDeriv_tsupport_subset (hφ : IsTestFunctionOn Ω φ) (i : Fin n) :
    tsupport (coordDeriv i φ) ⊆ Ω :=
  (tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans hφ.tsupport_subset

end IsTestFunctionOn

/-- Compactly supported multiplication turns local integrability on a domain into
global integrability. The multiplier's support must stay inside the domain. -/
theorem integrable_mul_of_locallyIntegrableOn {n : ℕ} {Ω : Set (Space n)}
    {u φ : Space n → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    Integrable (fun x => u x * φ x) volume := by
  have h : Integrable (fun x => φ x • u x) volume :=
    (integrableOn_iff_integrable_of_support_subset
      ((Function.support_smul_subset_left φ u).trans (subset_tsupport φ))).mp
      (((hu.integrableOn_compact_subset hs hc.isCompact).continuousOn_smul
        hφ.continuousOn) hc)
  simpa only [smul_eq_mul, mul_comm] using h

/-- A compactly supported factor makes restriction to a containing domain immaterial. -/
theorem setIntegral_mul_eq_integral_of_tsupport_subset {n : ℕ} {Ω : Set (Space n)}
    (u φ : Space n → ℝ) (hs : tsupport φ ⊆ Ω) :
    (∫ x in Ω, u x * φ x) = ∫ x, u x * φ x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), mul_zero]

/-- `du` represents the `i`-th distributional derivative of `u` on `Ω`.
Openness is required by uniqueness and calculus theorems, not by the predicate itself. -/
structure HasWeakPartialOn {n : ℕ} (Ω : Set (Space n)) (i : Fin n)
    (u du : Space n → ℝ) : Prop where
  locallyIntegrable : LocallyIntegrableOn u Ω volume
  derivative_locallyIntegrable : LocallyIntegrableOn du Ω volume
  integration_by_parts : ∀ φ : Space n → ℝ, IsTestFunctionOn Ω φ →
    (∫ x in Ω, u x * coordDeriv i φ x) = -(∫ x in Ω, du x * φ x)

namespace HasWeakPartialOn

variable {n : ℕ} {Ω Ω' : Set (Space n)} {i : Fin n} {u du v dv : Space n → ℝ}

/-- Equivalent global pairing for test functions supported inside the domain. -/
theorem integration_by_parts_global (hu : HasWeakPartialOn Ω i u du)
    {φ : Space n → ℝ} (hφ : IsTestFunctionOn Ω φ) :
    (∫ x, u x * coordDeriv i φ x) = -(∫ x, du x * φ x) := by
  have h := hu.integration_by_parts φ hφ
  rw [setIntegral_mul_eq_integral_of_tsupport_subset _ _ (hφ.coordDeriv_tsupport_subset i),
    setIntegral_mul_eq_integral_of_tsupport_subset _ _ hφ.tsupport_subset] at h
  exact h

theorem zero (Ω : Set (Space n)) (i : Fin n) :
    HasWeakPartialOn Ω i (fun _ => 0) (fun _ => 0) := by
  refine ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, ?_⟩
  intro φ _
  simp

theorem add (hu : HasWeakPartialOn Ω i u du) (hv : HasWeakPartialOn Ω i v dv) :
    HasWeakPartialOn Ω i (u + v) (du + dv) := by
  refine ⟨hu.locallyIntegrable.add hv.locallyIntegrable,
    hu.derivative_locallyIntegrable.add hv.derivative_locallyIntegrable, ?_⟩
  intro φ hφ
  have h1 := (integrable_mul_of_locallyIntegrableOn hu.locallyIntegrable
    (hφ.coordDeriv_continuous i) (hφ.coordDeriv_hasCompactSupport i)
    (hφ.coordDeriv_tsupport_subset i)).restrict (s := Ω)
  have h2 := (integrable_mul_of_locallyIntegrableOn hv.locallyIntegrable
    (hφ.coordDeriv_continuous i) (hφ.coordDeriv_hasCompactSupport i)
    (hφ.coordDeriv_tsupport_subset i)).restrict (s := Ω)
  have h3 := (integrable_mul_of_locallyIntegrableOn hu.derivative_locallyIntegrable
    hφ.contDiff.continuous hφ.hasCompactSupport hφ.tsupport_subset).restrict (s := Ω)
  have h4 := (integrable_mul_of_locallyIntegrableOn hv.derivative_locallyIntegrable
    hφ.contDiff.continuous hφ.hasCompactSupport hφ.tsupport_subset).restrict (s := Ω)
  simp only [Pi.add_apply, add_mul]
  rw [integral_add h1 h2, integral_add h3 h4,
    hu.integration_by_parts φ hφ, hv.integration_by_parts φ hφ]
  ring

theorem smul (hu : HasWeakPartialOn Ω i u du) (c : ℝ) :
    HasWeakPartialOn Ω i (c • u) (c • du) := by
  refine ⟨hu.locallyIntegrable.smul c, hu.derivative_locallyIntegrable.smul c, ?_⟩
  intro φ hφ
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  rw [hu.integration_by_parts φ hφ]
  ring

/-- The weak derivative relation depends only on the two a.e. classes on `Ω`. -/
theorem congr (hu : HasWeakPartialOn Ω i u du)
    (huv : u =ᵐ[volume.restrict Ω] v) (hd : du =ᵐ[volume.restrict Ω] dv) :
    HasWeakPartialOn Ω i v dv := by
  refine ⟨hu.locallyIntegrable.congr huv, hu.derivative_locallyIntegrable.congr hd, ?_⟩
  intro φ hφ
  have hleft : (∫ x in Ω, v x * coordDeriv i φ x) =
      ∫ x in Ω, u x * coordDeriv i φ x :=
    integral_congr_ae (huv.mono fun x hx => congrArg (fun a => a * coordDeriv i φ x) hx.symm)
  have hright : (∫ x in Ω, dv x * φ x) = ∫ x in Ω, du x * φ x :=
    integral_congr_ae (hd.mono fun x hx => congrArg (fun a => a * φ x) hx.symm)
  rw [hleft, hright]
  exact hu.integration_by_parts φ hφ

/-- Restricting a weak derivative to a smaller domain preserves its identity. -/
theorem mono (hu : HasWeakPartialOn Ω i u du) (hΩ : Ω' ⊆ Ω) :
    HasWeakPartialOn Ω' i u du := by
  refine ⟨hu.locallyIntegrable.mono_set hΩ,
    hu.derivative_locallyIntegrable.mono_set hΩ, ?_⟩
  intro φ hφ
  rw [setIntegral_mul_eq_integral_of_tsupport_subset _ _ (hφ.coordDeriv_tsupport_subset i),
    setIntegral_mul_eq_integral_of_tsupport_subset _ _ hφ.tsupport_subset]
  exact hu.integration_by_parts_global (hφ.mono hΩ)

/-- Distributional derivatives on an open domain are unique a.e. on that domain. -/
theorem unique (hΩ : IsOpen Ω) (hu : HasWeakPartialOn Ω i u du)
    (hv : HasWeakPartialOn Ω i u dv) : du =ᵐ[volume.restrict Ω] dv := by
  have hz : ∀ᵐ x ∂volume, x ∈ Ω → (du - dv) x = 0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hu.derivative_locallyIntegrable.sub hv.derivative_locallyIntegrable)
    intro φ hφ hc hs
    have ht : IsTestFunctionOn Ω φ := ⟨hφ, hc, hs⟩
    have heq : (∫ x, du x * φ x) = ∫ x, dv x * φ x := by
      exact neg_injective ((hu.integration_by_parts_global ht).symm.trans
        (hv.integration_by_parts_global ht))
    simp only [Pi.sub_apply, smul_eq_mul, mul_sub]
    rw [integral_sub]
    · simpa only [mul_comm, sub_eq_zero] using heq
    · simpa only [mul_comm] using integrable_mul_of_locallyIntegrableOn
        hu.derivative_locallyIntegrable hφ.continuous hc hs
    · simpa only [mul_comm] using integrable_mul_of_locallyIntegrableOn
        hv.derivative_locallyIntegrable hφ.continuous hc hs
  rw [Filter.EventuallyEq, ae_restrict_iff' hΩ.measurableSet]
  filter_upwards [hz] with x hx
  simpa only [Pi.sub_apply, sub_eq_zero] using hx

end HasWeakPartialOn

/-- Compatibility with the original whole-space interface. -/
theorem hasWeakPartialOn_univ_iff {n : ℕ} {i : Fin n} {u du : Space n → ℝ} :
    HasWeakPartialOn Set.univ i u du ↔ HasWeakPartial i u du := by
  constructor
  · intro h
    refine ⟨locallyIntegrableOn_univ.mp h.locallyIntegrable,
      locallyIntegrableOn_univ.mp h.derivative_locallyIntegrable, ?_⟩
    intro φ hφ hc
    simpa using h.integration_by_parts φ ⟨hφ, hc, subset_univ _⟩
  · intro h
    refine ⟨h.locallyIntegrable.locallyIntegrableOn _,
      h.derivative_locallyIntegrable.locallyIntegrableOn _, ?_⟩
    intro φ hφ
    simpa using h.integration_by_parts φ hφ.contDiff hφ.hasCompactSupport

end PDE
