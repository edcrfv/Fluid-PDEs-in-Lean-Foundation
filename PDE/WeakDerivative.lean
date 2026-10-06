import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring

/-!
# First weak derivatives on the whole space

This first interface uses real-valued, locally integrable representatives on `Fin n → ℝ`.
It tests against every compactly supported smooth function and records integrability explicitly.
Open-domain localization and the quotient norm/completeness construction are later milestones.
-/

open MeasureTheory
open scoped ContDiff

namespace PDE

abbrev Space (n : ℕ) := Fin n → ℝ

/-- The classical derivative in the `i`-th coordinate direction. -/
noncomputable def coordDeriv {n : ℕ} (i : Fin n) (φ : Space n → ℝ) (x : Space n) : ℝ :=
  fderiv ℝ φ x (Pi.single i 1)

/-- A first distributional derivative, represented by a locally integrable function. -/
structure HasWeakPartial {n : ℕ} (i : Fin n) (u du : Space n → ℝ) : Prop where
  locallyIntegrable : LocallyIntegrable u volume
  derivative_locallyIntegrable : LocallyIntegrable du volume
  integration_by_parts : ∀ φ : Space n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, u x * coordDeriv i φ x) = -(∫ x, du x * φ x)

namespace HasWeakPartial

variable {n : ℕ} {i : Fin n} {u du v dv : Space n → ℝ}

theorem zero (i : Fin n) : HasWeakPartial i (fun _ => 0) (fun _ => 0) := by
  refine ⟨locallyIntegrable_zero, locallyIntegrable_zero, ?_⟩
  intro φ _ _
  simp

private theorem integrable_pairing {f φ : Space n → ℝ}
    (hf : LocallyIntegrable f volume) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => f x * φ x) volume := by
  simpa only [smul_eq_mul] using hf.integrable_smul_right_of_hasCompactSupport hφ hc

private theorem partial_continuous {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (coordDeriv i φ) := by
  exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const

/-- Weak differentiation respects addition; the integrals are justified by compact support. -/
theorem add (hu : HasWeakPartial i u du) (hv : HasWeakPartial i v dv) :
    HasWeakPartial i (u + v) (du + dv) := by
  refine ⟨hu.locallyIntegrable.add hv.locallyIntegrable,
    hu.derivative_locallyIntegrable.add hv.derivative_locallyIntegrable, ?_⟩
  intro φ hφ hc
  have hpc : HasCompactSupport (coordDeriv i φ) := hc.fderiv_apply ℝ (Pi.single i 1)
  simp only [Pi.add_apply, add_mul]
  rw [integral_add
    (integrable_pairing hu.locallyIntegrable (partial_continuous hφ) hpc)
    (integrable_pairing hv.locallyIntegrable (partial_continuous hφ) hpc),
    integral_add
    (integrable_pairing hu.derivative_locallyIntegrable hφ.continuous hc)
    (integrable_pairing hv.derivative_locallyIntegrable hφ.continuous hc),
    hu.integration_by_parts φ hφ hc, hv.integration_by_parts φ hφ hc]
  ring

/-- Weak differentiation respects multiplication by a real constant. -/
theorem smul (hu : HasWeakPartial i u du) (c : ℝ) :
    HasWeakPartial i (c • u) (c • du) := by
  refine ⟨hu.locallyIntegrable.smul c, hu.derivative_locallyIntegrable.smul c, ?_⟩
  intro φ hφ hc
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  rw [hu.integration_by_parts φ hφ hc]
  ring

/-- A weak derivative is unique almost everywhere, rather than pointwise. -/
theorem unique (hu : HasWeakPartial i u du) (hv : HasWeakPartial i u dv) :
    du =ᵐ[volume] dv := by
  apply ae_eq_of_integral_contDiff_smul_eq hu.derivative_locallyIntegrable
    hv.derivative_locallyIntegrable
  intro φ hφ hc
  have h := (hu.integration_by_parts φ hφ hc).symm.trans
    (hv.integration_by_parts φ hφ hc)
  simpa only [neg_inj, smul_eq_mul, mul_comm] using h

end HasWeakPartial
end PDE
