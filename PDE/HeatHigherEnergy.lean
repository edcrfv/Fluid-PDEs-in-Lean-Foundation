import PDE.MassHigherEnergy
import PDE.HeatIntegratedGalerkin

/-!
# Finite heat regularity from the stiffness energy

Symmetry of the actual Dirichlet form gives exact dissipation of gradient energy by the
physical L² time derivative. Combining it with physical mass contraction proves contraction
of the full inherited H¹ norm. These results concern the constructed finite trajectories.
-/

open InnerProductSpace MeasureTheory Set Filter
open scoped Topology ENNReal
namespace PDE
variable {n : ℕ} {Ω : Set (Space n)} {hΩ : IsOpen Ω}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] trialNormedAddCommGroup trialSeminormedAddCommGroup
  trialNormedSpace trialInnerProductSpace trialDualTopology

/-- The actual physical L² derivative of a finite heat trajectory. -/
noncomputable def heatGalerkinVelocity (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (u₀ : S) : ℝ → DomainL2 Ω :=
  massVelocity (trialValue S) (trialValue_injective S) (trialDirichletForm S) u₀

theorem heatGalerkinVelocity_hasDerivAt (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (u₀ : S) (t : ℝ) :
    HasDerivAt (fun t => trialValue S (heatGalerkin S u₀ t)) (heatGalerkinVelocity S u₀ t) t := by
  unfold heatGalerkin heatGalerkinVelocity
  exact massVelocity_hasDerivAt (V := S) (trialValue S) (trialValue_injective S)
    (trialDirichletForm S) u₀ t

theorem heatGalerkinVelocity_continuous (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (u₀ : S) : Continuous (heatGalerkinVelocity S u₀) := by
  unfold heatGalerkinVelocity
  exact massVelocity_continuous (V := S) (trialValue S) (trialValue_injective S)
    (trialDirichletForm S) u₀

theorem heatGalerkin_stiffness_energy_identity (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (u₀ : S) (T : ℝ) :
    dirichletForm Ω hΩ (heatGalerkin S u₀ T).val (heatGalerkin S u₀ T).val +
      2 * (∫ t in (0 : ℝ)..T, ‖heatGalerkinVelocity S u₀ t‖ ^ 2) =
        dirichletForm Ω hΩ u₀.val u₀.val := by
  unfold heatGalerkin heatGalerkinVelocity
  exact massEvolution_stiffness_energy_identity (V := S) (trialValue S) (trialValue_injective S)
    (trialDirichletForm S) (fun u v => dirichletForm_symm u.val v.val) u₀ T

theorem heatGalerkin_integrated_velocity_le (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (u₀ : S) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, ‖heatGalerkinVelocity S u₀ t‖ ^ 2) ≤
      dirichletForm Ω hΩ u₀.val u₀.val / 2 := by
  unfold heatGalerkinVelocity
  exact massEvolution_integrated_velocity_le (V := S) (trialValue S) (trialValue_injective S)
    (trialDirichletForm S) (fun u v => dirichletForm_symm u.val v.val)
    (trialDirichletForm_nonneg S) u₀ T

theorem heatGalerkin_stiffness_le (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (u₀ : S) {T : ℝ} (hT : 0 ≤ T) :
    dirichletForm Ω hΩ (heatGalerkin S u₀ T).val (heatGalerkin S u₀ T).val ≤
      dirichletForm Ω hΩ u₀.val u₀.val := by
  unfold heatGalerkin
  exact massEvolution_stiffness_le (V := S) (trialValue S) (trialValue_injective S)
    (trialDirichletForm S) (fun u v => dirichletForm_symm u.val v.val) u₀ hT

/-- The full inherited H¹ norm also contracts along each finite heat trajectory. -/
theorem heatGalerkin_H1norm_le (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (u₀ : S) {T : ℝ} (hT : 0 ≤ T) :
    ‖heatGalerkin S u₀ T‖ ≤ ‖u₀‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(heatGalerkin S u₀ T).val‖ ^ 2 ≤ ‖u₀.val‖ ^ 2
  rw [H10.norm_sq_eq_value_add_dirichlet, H10.norm_sq_eq_value_add_dirichlet]
  apply add_le_add _ (heatGalerkin_stiffness_le S u₀ hT)
  exact pow_le_pow_left₀ (norm_nonneg _) (heatGalerkin_norm_le S u₀ hT) 2
end PDE
