import PDE.SobolevH1
import PDE.ClassicalWeakDerivative
import Mathlib.Topology.Sequences

/-!
# The zero-boundary energy space

`H10 Ω hΩ` is the closure in H¹ of smooth functions compactly supported in the open domain.
It inherits the full H¹ norm and is complete. A sequence of actual test functions converges
to every element. No boundary trace identification is assumed or asserted.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace PDE

variable {n : ℕ} {Ω : Set (Space n)}

/-- The algebraic vector space of scalar test functions on a domain. -/
def testFunctionSubspace (Ω : Set (Space n)) : Submodule ℝ (Space n → ℝ) where
  carrier := {φ | IsTestFunctionOn Ω φ}
  zero_mem' := IsTestFunctionOn.zero Ω
  add_mem' := IsTestFunctionOn.add
  smul_mem' := fun c _ h => h.smul c

namespace H1

/-- Smooth compactly supported functions give actual elements of the Sobolev graph. -/
noncomputable def ofTestFunction (φ : Space n → ℝ) (hφ : IsTestFunctionOn Ω φ) : H1 Ω :=
  ofFunction φ (fun i => coordDeriv i φ)
    (hφ.contDiff.continuous.memLp_of_hasCompactSupport hφ.hasCompactSupport)
    (fun i => (hφ.coordDeriv_continuous i).memLp_of_hasCompactSupport
      (hφ.coordDeriv_hasCompactSupport i))
    (fun i => (hasWeakPartialOn_univ_iff.mpr
      (hasWeakPartial_of_contDiff i (hφ.contDiff.of_le (by simp)))).mono (subset_univ Ω))

theorem value_ofTestFunction_ae (φ : Space n → ℝ) (hφ : IsTestFunctionOn Ω φ) :
    value Ω (ofTestFunction φ hφ) =ᵐ[volume.restrict Ω] φ :=
  value_ofFunction_ae _ _ _ _ _

theorem derivative_ofTestFunction_ae (φ : Space n → ℝ)
    (hφ : IsTestFunctionOn Ω φ) (i : Fin n) :
    derivative Ω i (ofTestFunction φ hφ) =ᵐ[volume.restrict Ω] coordDeriv i φ :=
  derivative_ofFunction_ae _ _ _ _ _ i

theorem norm_value_ofTestFunction (φ : Space n → ℝ) (hφ : IsTestFunctionOn Ω φ) :
    ‖value Ω (ofTestFunction φ hφ)‖ = (eLpNorm φ 2 volume).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (value_ofTestFunction_ae φ hφ),
    eLpNorm_restrict_eq_of_support_subset ((subset_tsupport φ).trans hφ.tsupport_subset)]

theorem norm_derivative_ofTestFunction (φ : Space n → ℝ)
    (hφ : IsTestFunctionOn Ω φ) (i : Fin n) :
    ‖derivative Ω i (ofTestFunction φ hφ)‖ =
      (eLpNorm (coordDeriv i φ) 2 volume).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (derivative_ofTestFunction_ae φ hφ i),
    eLpNorm_restrict_eq_of_support_subset
      ((subset_tsupport _).trans (hφ.coordDeriv_tsupport_subset i))]

end H1

/-- The canonical linear embedding of test functions in the Sobolev graph. -/
noncomputable def testFunctionToH1 (Ω : Set (Space n)) (hΩ : IsOpen Ω) :
    testFunctionSubspace Ω →ₗ[ℝ] H1 Ω where
  toFun φ := H1.ofTestFunction φ φ.property
  map_add' φ ψ := by
    apply H1.value_injective hΩ
    rw [map_add]
    apply Lp.ext
    exact (H1.value_ofTestFunction_ae _ _).trans
      ((Lp.coeFn_add _ _).trans
        ((H1.value_ofTestFunction_ae _ _).add (H1.value_ofTestFunction_ae _ _))).symm
  map_smul' c φ := by
    apply H1.value_injective hΩ
    rw [map_smul]
    apply Lp.ext
    exact (H1.value_ofTestFunction_ae _ _).trans
      ((Lp.coeFn_smul c _).trans
        ((H1.value_ofTestFunction_ae _ _).const_smul c)).symm

/-- H¹ closure of the smooth compact-support image. -/
noncomputable def h10Subspace (Ω : Set (Space n)) (hΩ : IsOpen Ω) : Submodule ℝ (H1 Ω) :=
  (testFunctionToH1 Ω hΩ).range.topologicalClosure

abbrev H10 (Ω : Set (Space n)) (hΩ : IsOpen Ω) := ↥(h10Subspace Ω hΩ)

noncomputable instance h10CompleteSpace (Ω : Set (Space n)) (hΩ : IsOpen Ω) :
    CompleteSpace (H10 Ω hΩ) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

namespace H10

variable {hΩ : IsOpen Ω}

noncomputable def toH1 (Ω : Set (Space n)) (hΩ : IsOpen Ω) : H10 Ω hΩ →L[ℝ] H1 Ω :=
  (h10Subspace Ω hΩ).subtypeL

/-- An actual smooth test function as a zero-boundary energy-space element. -/
noncomputable def ofTestFunction (hΩ : IsOpen Ω) (φ : Space n → ℝ)
    (hφ : IsTestFunctionOn Ω φ) : H10 Ω hΩ :=
  ⟨H1.ofTestFunction φ hφ, Submodule.le_topologicalClosure _ ⟨⟨φ, hφ⟩, rfl⟩⟩

/-- Smooth compact-support approximation in the full H¹ norm. -/
theorem exists_testFunction_sequence (u : H10 Ω hΩ) :
    ∃ φ : ℕ → testFunctionSubspace Ω,
      Tendsto (fun k => H1.ofTestFunction (Ω := Ω) (φ k) (φ k).property)
        atTop (𝓝 u.val) := by
  have hu : u.val ∈ closure (Set.range (testFunctionToH1 Ω hΩ)) := u.property
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp hu
  choose φ hφ using hv
  refine ⟨φ, ?_⟩
  have heq : (fun k => H1.ofTestFunction (Ω := Ω) (φ k) (φ k).property) = v :=
    funext hφ
  rwa [heq]

/-- A closed condition verified for every test function extends to all of H₀¹. -/
theorem induction_of_isClosed {s : Set (H1 Ω)} (hs : IsClosed s)
    (ht : ∀ φ (hφ : IsTestFunctionOn Ω φ), H1.ofTestFunction φ hφ ∈ s)
    (u : H10 Ω hΩ) : u.val ∈ s := by
  apply closure_minimal (s := Set.range (testFunctionToH1 Ω hΩ)) ?_ hs u.property
  rintro _ ⟨φ, rfl⟩
  exact ht φ φ.property

end H10
end PDE
