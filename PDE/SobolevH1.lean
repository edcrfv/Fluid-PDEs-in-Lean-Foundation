import PDE.WeakDerivativeOn
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# A complete first-order Sobolev graph space

The ambient Hilbert space is the finite L² product of the function and its partial derivatives.
Each weak derivative equation is the kernel of a continuous linear test-functional.
Their intersection is closed, hence a Hilbert space. For an open domain, a.e. uniqueness
of weak derivatives makes the projection to the value component injective.

All components are genuine L² a.e. classes; the graph norm is the usual sum-of-squares norm.
-/

open MeasureTheory InnerProductSpace Set
open scoped ENNReal

namespace PDE

noncomputable abbrev DomainL2 {n : ℕ} (Ω : Set (Space n)) := Lp ℝ 2 (volume.restrict Ω)

/-- A finite Hilbert product: component zero is the value, successor components are derivatives. -/
abbrev H1Ambient {n : ℕ} (Ω : Set (Space n)) :=
  PiLp 2 (fun _ : Fin (n + 1) => DomainL2 Ω)

/-- Integration against a continuous compactly supported scalar function as an L² functional. -/
noncomputable def testPairing {n : ℕ} (Ω : Set (Space n)) (φ : Space n → ℝ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) : DomainL2 Ω →L[ℝ] ℝ :=
  innerSL ℝ ((hφ.memLp_of_hasCompactSupport hc : MemLp φ 2 (volume.restrict Ω)).toLp φ)

theorem testPairing_apply {n : ℕ} (Ω : Set (Space n)) (φ : Space n → ℝ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (u : DomainL2 Ω) :
    testPairing Ω φ hφ hc u = ∫ x in Ω, u x * φ x := by
  change inner ℝ ((hφ.memLp_of_hasCompactSupport hc :
    MemLp φ 2 (volume.restrict Ω)).toLp φ) u = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hφ.memLp_of_hasCompactSupport hc :
    MemLp φ 2 (volume.restrict Ω)).coeFn_toLp] with x hx
  simp [hx, mul_comm]

/-- The residual of the `i`-th weak derivative identity against a test function. -/
noncomputable def weakResidual {n : ℕ} (Ω : Set (Space n)) (i : Fin n)
    (φ : Space n → ℝ) (hφ : IsTestFunctionOn Ω φ) : H1Ambient Ω →L[ℝ] ℝ :=
  (testPairing Ω (coordDeriv i φ) (hφ.coordDeriv_continuous i)
    (hφ.coordDeriv_hasCompactSupport i)).comp (PiLp.proj 2 _ 0) +
  (testPairing Ω φ hφ.contDiff.continuous hφ.hasCompactSupport).comp
    (PiLp.proj 2 _ i.succ)

theorem weakResidual_apply {n : ℕ} (Ω : Set (Space n)) (i : Fin n)
    (φ : Space n → ℝ) (hφ : IsTestFunctionOn Ω φ) (U : H1Ambient Ω) :
    weakResidual Ω i φ hφ U =
      (∫ x in Ω, U 0 x * coordDeriv i φ x) + (∫ x in Ω, U i.succ x * φ x) := by
  change testPairing Ω (coordDeriv i φ) (hφ.coordDeriv_continuous i)
    (hφ.coordDeriv_hasCompactSupport i) (U 0) +
    testPairing Ω φ hφ.contDiff.continuous hφ.hasCompactSupport (U i.succ) = _
  rw [testPairing_apply, testPairing_apply]

/-- The closed graph of all first weak partial derivatives in the L² product. -/
noncomputable def h1Subspace {n : ℕ} (Ω : Set (Space n)) : Submodule ℝ (H1Ambient Ω) :=
  ⨅ (i : Fin n) (φ : Space n → ℝ) (hφ : IsTestFunctionOn Ω φ),
    (weakResidual Ω i φ hφ).ker

theorem mem_h1Subspace_iff {n : ℕ} {Ω : Set (Space n)} {U : H1Ambient Ω} :
    U ∈ h1Subspace Ω ↔ ∀ i, HasWeakPartialOn Ω i (U 0) (U i.succ) := by
  simp only [h1Subspace, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h i
    refine ⟨locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp (U 0)).locallyIntegrable (by norm_num)),
      locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp (U i.succ)).locallyIntegrable (by norm_num)), ?_⟩
    intro φ hφ
    have hh := h i φ hφ
    change weakResidual Ω i φ hφ U = 0 at hh
    rw [weakResidual_apply] at hh
    exact eq_neg_iff_add_eq_zero.mpr hh
  · intro h i φ hφ
    change weakResidual Ω i φ hφ U = 0
    rw [weakResidual_apply, (h i).integration_by_parts φ hφ]
    simp

theorem h1Subspace_isClosed {n : ℕ} (Ω : Set (Space n)) :
    IsClosed (h1Subspace Ω : Set (H1Ambient Ω)) := by
  simp only [h1Subspace, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun φ => isClosed_iInter fun hφ =>
    (weakResidual Ω i φ hφ).isClosed_ker

/-- First-order L² Sobolev functions, represented by their closed weak-derivative graph. -/
abbrev H1 {n : ℕ} (Ω : Set (Space n)) := ↥(h1Subspace Ω)

noncomputable instance h1CompleteSpace {n : ℕ} (Ω : Set (Space n)) : CompleteSpace (H1 Ω) :=
  (h1Subspace_isClosed Ω).completeSpace_coe

namespace H1

variable {n : ℕ} {Ω : Set (Space n)}

/-- The L² a.e. class of a Sobolev function. -/
noncomputable def value (Ω : Set (Space n)) : H1 Ω →L[ℝ] DomainL2 Ω :=
  (PiLp.proj 2 _ 0).comp (h1Subspace Ω).subtypeL

/-- The `i`-th L² weak derivative as a continuous linear operator on H¹. -/
noncomputable def derivative (Ω : Set (Space n)) (i : Fin n) : H1 Ω →L[ℝ] DomainL2 Ω :=
  (PiLp.proj 2 _ i.succ).comp (h1Subspace Ω).subtypeL

theorem hasWeakPartialOn (u : H1 Ω) (i : Fin n) :
    HasWeakPartialOn Ω i (value Ω u) (derivative Ω i u) :=
  (mem_h1Subspace_iff.mp u.property) i

/-- Equality of the value classes determines the whole graph on an open domain. -/
theorem value_injective (hΩ : IsOpen Ω) : Function.Injective (value Ω) := by
  intro u v huv
  apply Subtype.ext
  apply PiLp.ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact huv
  · apply Lp.ext
    have h := v.hasWeakPartialOn i
    rw [← huv] at h
    exact (u.hasWeakPartialOn i).unique hΩ h

/-- The H¹ norm contains the L² norm and the squared L² norms of all weak derivatives. -/
theorem norm_sq_eq (u : H1 Ω) :
    ‖u‖ ^ 2 = ‖value Ω u‖ ^ 2 + ∑ i : Fin n, ‖derivative Ω i u‖ ^ 2 := by
  change ‖u.val‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  rfl

/-- The integral of the physical sum of squared weak partials equals the
sum of their L² class norms. The ambient spatial sup norm is not used here. -/
theorem integral_gradient_sq (u : H1 Ω) :
    (∫ x in Ω, ∑ i : Fin n, H1.derivative Ω i u x ^ 2) =
      ∑ i : Fin n, ‖H1.derivative Ω i u‖ ^ 2 := by
  rw [integral_finsetSum _ (fun i _ => (Lp.memLp (H1.derivative Ω i u)).integrable_sq)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp [pow_two]

theorem norm_value_le (u : H1 Ω) : ‖value Ω u‖ ≤ ‖u‖ :=
  PiLp.norm_apply_le u.val 0

theorem norm_derivative_le (u : H1 Ω) (i : Fin n) : ‖derivative Ω i u‖ ≤ ‖u‖ :=
  PiLp.norm_apply_le u.val i.succ

/-- Construct the Sobolev a.e. class from an L² function and its L² weak derivatives. -/
noncomputable def ofFunction (u : Space n → ℝ) (du : Fin n → Space n → ℝ)
    (hu : MemLp u 2 (volume.restrict Ω))
    (hd : ∀ i, MemLp (du i) 2 (volume.restrict Ω))
    (hw : ∀ i, HasWeakPartialOn Ω i u (du i)) : H1 Ω := by
  let U : H1Ambient Ω := WithLp.toLp 2 (Fin.cases (hu.toLp u) fun i => (hd i).toLp (du i))
  refine ⟨U, mem_h1Subspace_iff.mpr fun i => ?_⟩
  exact (hw i).congr hu.coeFn_toLp.symm (hd i).coeFn_toLp.symm

theorem value_ofFunction_ae (u : Space n → ℝ) (du : Fin n → Space n → ℝ)
    (hu : MemLp u 2 (volume.restrict Ω))
    (hd : ∀ i, MemLp (du i) 2 (volume.restrict Ω))
    (hw : ∀ i, HasWeakPartialOn Ω i u (du i)) :
    value Ω (ofFunction u du hu hd hw) =ᵐ[volume.restrict Ω] u := hu.coeFn_toLp

theorem derivative_ofFunction_ae (u : Space n → ℝ) (du : Fin n → Space n → ℝ)
    (hu : MemLp u 2 (volume.restrict Ω))
    (hd : ∀ i, MemLp (du i) 2 (volume.restrict Ω))
    (hw : ∀ i, HasWeakPartialOn Ω i u (du i)) (i : Fin n) :
    derivative Ω i (ofFunction u du hu hd hw) =ᵐ[volume.restrict Ω] du i :=
  (hd i).coeFn_toLp

end H1
end PDE
