import PDE.HeatHigherEnergy

/-!
# H¹-stable initial data for heat Galerkin approximation

For H₀¹ data, use the proved mass-projection API with the inherited H¹ inclusion. This
produces an H¹ orthogonal projection, its full-norm contraction and strong convergence.
Evolving these initial data gives uniform H¹ state and physical L² velocity estimates.
No H¹ stability of the separate physical L² initial projection is assumed.
-/

open InnerProductSpace MeasureTheory Set Filter
open scoped Topology ENNReal
namespace PDE
variable {n : ℕ} {Ω : Set (Space n)} {hΩ : IsOpen Ω}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] trialNormedAddCommGroup trialSeminormedAddCommGroup
  trialNormedSpace trialInnerProductSpace trialDualTopology

/-- The inherited inclusion of a trial space into the complete H¹ energy space. -/
noncomputable def trialH1Inclusion (S : Submodule ℝ (H10 Ω hΩ)) : S →L[ℝ] H10 Ω hΩ :=
  S.subtypeL

theorem trialH1Inclusion_injective (S : Submodule ℝ (H10 Ω hΩ)) :
    Function.Injective (trialH1Inclusion S) := Subtype.val_injective

/-- Orthogonal projection in the full H¹ norm for H₀¹ initial data. -/
noncomputable def heatH1InitialProjection (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (h : H10 Ω hΩ) : S := massProjection (V := S) (H := H10 Ω hΩ) (trialH1Inclusion S) (trialH1Inclusion_injective S) h

theorem heatH1InitialProjection_norm_le (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (h : H10 Ω hΩ) : ‖heatH1InitialProjection S h‖ ≤ ‖h‖ := by
  simpa only [heatH1InitialProjection, trialH1Inclusion] using!
    (massProjection_norm_le (V := S) (H := H10 Ω hΩ)
      (trialH1Inclusion S) (trialH1Inclusion_injective S) h)

theorem heatH1InitialProjection_bestApproximation (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (h : H10 Ω hΩ) (v : S) :
    ‖h - (heatH1InitialProjection S h).val‖ ≤ ‖h - v.val‖ := by
  simpa only [heatH1InitialProjection, trialH1Inclusion] using!
    (massProjection_bestApproximation (V := S) (H := H10 Ω hΩ)
      (trialH1Inclusion S) (trialH1Inclusion_injective S) h v)

/-- Nested H¹-dense spaces approximate H₀¹ data in their full norm. -/
theorem heatH1InitialProjection_tendsto (S : ℕ → Submodule ℝ (H10 Ω hΩ))
    [∀ k, FiniteDimensional ℝ (S k)] (hS : Monotone S)
    (hd : Dense (⋃ k, (S k : Set (H10 Ω hΩ)))) (h : H10 Ω hΩ) :
    Tendsto (fun k => (heatH1InitialProjection (S k) h).val) atTop (𝓝 h) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_exists_trial_approximation (V := H10 Ω hΩ) S hS hd h hε
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨v, hv, herr⟩ := hN k hk
  rw [dist_eq_norm, norm_sub_rev]
  exact (heatH1InitialProjection_bestApproximation (S k) h ⟨v, hv⟩).trans_lt herr

theorem heatH1InitialProjection_value_tendsto (S : ℕ → Submodule ℝ (H10 Ω hΩ))
    [∀ k, FiniteDimensional ℝ (S k)] (hS : Monotone S)
    (hd : Dense (⋃ k, (S k : Set (H10 Ω hΩ)))) (h : H10 Ω hΩ) :
    Tendsto (fun k => trialValue (S k) (heatH1InitialProjection (S k) h)) atTop
      (𝓝 (H10.value Ω hΩ h)) :=
  (H10.value Ω hΩ).continuous.continuousAt.tendsto.comp
    (heatH1InitialProjection_tendsto S hS hd h)
/-- The finite heat trajectory initialized by the full H¹ projection. -/
noncomputable def heatH1Trajectory (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (h : H10 Ω hΩ) (t : ℝ) : H10 Ω hΩ :=
  (heatGalerkin S (heatH1InitialProjection S h) t).val

noncomputable def heatH1Velocity (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (h : H10 Ω hΩ) : ℝ → DomainL2 Ω :=
  heatGalerkinVelocity S (heatH1InitialProjection S h)

theorem heatH1Trajectory_zero (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (h : H10 Ω hΩ) :
    heatH1Trajectory S h 0 = (heatH1InitialProjection S h).val := by
  unfold heatH1Trajectory
  rw [heatGalerkin_zero]

theorem heatH1Trajectory_continuous (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (h : H10 Ω hΩ) : Continuous (heatH1Trajectory S h) :=
  S.subtypeL.continuous.comp (heatGalerkin_continuous S _)

theorem heatH1Velocity_continuous (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (h : H10 Ω hΩ) : Continuous (heatH1Velocity S h) :=
  heatGalerkinVelocity_continuous S _

theorem heatH1Velocity_hasDerivAt (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (h : H10 Ω hΩ) (t : ℝ) :
    HasDerivAt (fun t => H10.value Ω hΩ (heatH1Trajectory S h t)) (heatH1Velocity S h t) t :=
  heatGalerkinVelocity_hasDerivAt S _ t

theorem heatH1Trajectory_norm_le (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (h : H10 Ω hΩ) {t : ℝ} (ht : 0 ≤ t) :
    ‖heatH1Trajectory S h t‖ ≤ ‖h‖ :=
  (heatGalerkin_H1norm_le S _ ht).trans (heatH1InitialProjection_norm_le S h)

/-- The derivative bound is independent of the trial dimension. -/
theorem heatH1Velocity_integrated_norm_sq_le (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (h : H10 Ω hΩ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, ‖heatH1Velocity S h t‖ ^ 2) ≤ ‖h‖ ^ 2 / 2 := by
  have he := heatGalerkin_integrated_velocity_le S (heatH1InitialProjection S h) T
  have hn := H10.norm_sq_eq_value_add_dirichlet (heatH1InitialProjection S h).val
  have hp := pow_le_pow_left₀ (norm_nonneg _) (heatH1InitialProjection_norm_le S h) 2
  change ‖(heatH1InitialProjection S h).val‖ ^ 2 ≤ ‖h‖ ^ 2 at hp
  change (∫ t in (0 : ℝ)..T, ‖heatH1Velocity S h t‖ ^ 2) ≤ _ at he
  nlinarith [sq_nonneg ‖H10.value Ω hΩ (heatH1InitialProjection S h).val‖]
end PDE
