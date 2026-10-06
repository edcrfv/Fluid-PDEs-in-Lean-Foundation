import PDE.MassEvolution
import PDE.EllipticWeakSolutions

/-!
# Constructed finite-dimensional heat Galerkin solutions

For any finite-dimensional subspace of H₀¹ on any open domain, the actual L² mass map
and Dirichlet stiffness form produce a global homogeneous heat Galerkin trajectory.
The weak equation, exact physical energy identity, L² contraction and integrated gradient
bound are proved. No passage to an infinite-dimensional heat solution is asserted here.

The local instances below spell out the inherited trial-space structures to avoid deep
instance-search ambiguity in nested Sobolev subspaces. They preserve the original norms.
-/

open InnerProductSpace MeasureTheory Set
namespace PDE
variable {n : ℕ} {Ω : Set (Space n)} {hΩ : IsOpen Ω}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable local instance trialNormedAddCommGroup (S : Submodule ℝ (H10 Ω hΩ)) :
    NormedAddCommGroup S := inferInstanceAs (NormedAddCommGroup ↥S)
noncomputable local instance trialSeminormedAddCommGroup (S : Submodule ℝ (H10 Ω hΩ)) :
    SeminormedAddCommGroup S := (trialNormedAddCommGroup S).toSeminormedAddCommGroup
noncomputable local instance trialNormedSpace (S : Submodule ℝ (H10 Ω hΩ)) : NormedSpace ℝ S :=
  S.normedSpace
noncomputable local instance trialInnerProductSpace (S : Submodule ℝ (H10 Ω hΩ)) :
    InnerProductSpace ℝ S := Submodule.innerProductSpace (𝕜 := ℝ) (E := H10 Ω hΩ) S

noncomputable local instance trialDualTopology (S : Submodule ℝ (H10 Ω hΩ)) :
    TopologicalSpace (S →L[ℝ] ℝ) :=
  ContinuousLinearMap.topologicalSpace (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ) (E := S) (F := ℝ)

/-- The actual L² value map of a zero-boundary trial space. -/
noncomputable def trialValue (S : Submodule ℝ (H10 Ω hΩ)) : S →L[ℝ] DomainL2 Ω :=
  (H1.value Ω).comp ((H10.toH1 Ω hΩ).comp S.subtypeL)

theorem trialValue_apply (S : Submodule ℝ (H10 Ω hΩ)) (u : S) :
    trialValue S u = H1.value Ω u.val.val := rfl

theorem trialValue_injective (S : Submodule ℝ (H10 Ω hΩ)) : Function.Injective (trialValue S) := by
  intro u v huv
  apply Subtype.ext
  apply Subtype.ext
  exact H1.value_injective hΩ huv

noncomputable def trialDirichletForm (S : Submodule ℝ (H10 Ω hΩ)) : S →L[ℝ] S →L[ℝ] ℝ :=
  (dirichletForm Ω hΩ).bilinearComp S.subtypeL S.subtypeL

theorem trialDirichletForm_apply (S : Submodule ℝ (H10 Ω hΩ)) (u v : S) :
    trialDirichletForm S u v = dirichletForm Ω hΩ u.val v.val := rfl

theorem trialDirichletForm_nonneg (S : Submodule ℝ (H10 Ω hΩ)) (u : S) :
    0 ≤ trialDirichletForm S u u := by
  rw [trialDirichletForm_apply, dirichletForm_self]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- A constructed homogeneous heat Galerkin trajectory in any finite-dimensional H₀¹ subspace. -/
noncomputable def heatGalerkin (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (u₀ : S) : ℝ → S :=
  massEvolution (trialValue S) (trialValue_injective S) (trialDirichletForm S) u₀

theorem heatGalerkin_zero (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (u₀ : S) : heatGalerkin S u₀ 0 = u₀ := by
  unfold heatGalerkin
  exact massEvolution_zero (V := S) (trialValue S) (trialValue_injective S) (trialDirichletForm S) u₀

/-- The heat equation uses the L² mass pairing and the Dirichlet stiffness pairing. -/
theorem heatGalerkin_weakEquation (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (u₀ v : S) (t : ℝ) :
    HasDerivAt (fun s => inner ℝ (trialValue S (heatGalerkin S u₀ s)) (trialValue S v))
      (-(dirichletForm Ω hΩ (heatGalerkin S u₀ t).val v.val)) t :=
  by
  unfold heatGalerkin
  exact massEvolution_weakEquation (V := S) (trialValue S) (trialValue_injective S)
    (trialDirichletForm S) u₀ v t

/-- Exact physical L² energy dissipation for the constructed heat Galerkin solution. -/
theorem heatGalerkin_energy_identity (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (u₀ : S) (T : ℝ) :
    ‖trialValue S (heatGalerkin S u₀ T)‖ ^ 2 +
      2 * (∫ t in (0 : ℝ)..T,
        dirichletForm Ω hΩ (heatGalerkin S u₀ t).val (heatGalerkin S u₀ t).val) =
          ‖trialValue S u₀‖ ^ 2 :=
  by
  unfold heatGalerkin
  exact massEvolution_energy_identity (V := S) (trialValue S) (trialValue_injective S)
    (trialDirichletForm S) u₀ T

/-- The L² estimate has the same constant 1 in every trial dimension. -/
theorem heatGalerkin_norm_le (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (u₀ : S) {T : ℝ} (hT : 0 ≤ T) : ‖trialValue S (heatGalerkin S u₀ T)‖ ≤ ‖trialValue S u₀‖ :=
  by
  unfold heatGalerkin
  exact massEvolution_norm_le (V := S) (trialValue S) (trialValue_injective S)
    (trialDirichletForm S) (trialDirichletForm_nonneg S) u₀ hT

/-- Integrated gradient energy is also bounded uniformly in the trial dimension. -/
theorem heatGalerkin_integrated_energy_le (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (u₀ : S) (T : ℝ) :
    (∫ t in (0 : ℝ)..T,
      dirichletForm Ω hΩ (heatGalerkin S u₀ t).val (heatGalerkin S u₀ t).val) ≤
        ‖trialValue S u₀‖ ^ 2 / 2 := by
  have he := heatGalerkin_energy_identity S u₀ T
  nlinarith [sq_nonneg ‖trialValue S (heatGalerkin S u₀ T)‖]
end PDE
