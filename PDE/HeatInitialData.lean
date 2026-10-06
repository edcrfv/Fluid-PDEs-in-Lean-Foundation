import PDE.HeatGalerkin
import PDE.MassProjection
import PDE.SobolevDensity
import PDE.GalerkinConvergence

/-!
# Heat Galerkin evolution from arbitrary L² initial data

The physical mass projection is norm decreasing and is a best approximation.
For nested H¹-dense trial spaces these projections converge strongly in L² to every
L² datum, using the proved density of H₀¹ in L². The resulting finite trajectories
satisfy energy estimates with constants independent of the trial dimension.
-/

open InnerProductSpace MeasureTheory Set Filter
open scoped Topology
namespace PDE
variable {n : ℕ} {Ω : Set (Space n)} {hΩ : IsOpen Ω}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] trialNormedAddCommGroup trialSeminormedAddCommGroup
  trialNormedSpace trialInnerProductSpace trialDualTopology

noncomputable def heatInitialProjection (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (f : DomainL2 Ω) : S := massProjection (trialValue S) (trialValue_injective S) f

theorem heatInitialProjection_norm_le (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (f : DomainL2 Ω) : ‖trialValue S (heatInitialProjection S f)‖ ≤ ‖f‖ := by
  unfold heatInitialProjection
  exact massProjection_norm_le (V := S) (trialValue S) (trialValue_injective S) f

theorem heatInitialProjection_bestApproximation (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (f : DomainL2 Ω) (v : S) :
    ‖f - trialValue S (heatInitialProjection S f)‖ ≤ ‖f - trialValue S v‖ := by
  unfold heatInitialProjection
  exact massProjection_bestApproximation (V := S) (trialValue S) (trialValue_injective S) f v

noncomputable def heatGalerkinFromL2 (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (f : DomainL2 Ω) : ℝ → S := heatGalerkin S (heatInitialProjection S f)

theorem heatGalerkinFromL2_zero (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (f : DomainL2 Ω) : heatGalerkinFromL2 S f 0 = heatInitialProjection S f :=
  heatGalerkin_zero S _

theorem heatGalerkinFromL2_energy_le (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (f : DomainL2 Ω) (T : ℝ) :
    ‖trialValue S (heatGalerkinFromL2 S f T)‖ ^ 2 +
      2 * (∫ t in (0 : ℝ)..T,
        dirichletForm Ω hΩ (heatGalerkinFromL2 S f t).val (heatGalerkinFromL2 S f t).val) ≤
          ‖f‖ ^ 2 := by
  unfold heatGalerkinFromL2
  rw [heatGalerkin_energy_identity]
  exact pow_le_pow_left₀ (norm_nonneg _) (heatInitialProjection_norm_le S f) 2

theorem heatGalerkinFromL2_norm_le (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (f : DomainL2 Ω) {T : ℝ} (hT : 0 ≤ T) : ‖trialValue S (heatGalerkinFromL2 S f T)‖ ≤ ‖f‖ :=
  (heatGalerkin_norm_le S _ hT).trans (heatInitialProjection_norm_le S f)

theorem heatGalerkinFromL2_integrated_energy_le (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (f : DomainL2 Ω) (T : ℝ) :
    (∫ t in (0 : ℝ)..T,
      dirichletForm Ω hΩ (heatGalerkinFromL2 S f t).val (heatGalerkinFromL2 S f t).val) ≤
        ‖f‖ ^ 2 / 2 := by
  have he := heatGalerkinFromL2_energy_le S f T
  nlinarith [sq_nonneg ‖trialValue S (heatGalerkinFromL2 S f T)‖]

/-- H¹-dense nested trial spaces also approximate every L² datum in the physical norm. -/
theorem eventually_exists_trial_L2approximation (S : ℕ → Submodule ℝ (H10 Ω hΩ))
    (hS : Monotone S) (hd : Dense (⋃ k, (S k : Set (H10 Ω hΩ)))) (f : DomainL2 Ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ k ≥ N, ∃ v : S k, ‖f - trialValue (S k) v‖ < ε := by
  obtain ⟨g, ⟨u, rfl⟩, hu⟩ :=
    Metric.mem_closure_iff.mp (H10.value_denseRange Ω hΩ f) (ε / 2) (half_pos hε)
  rw [dist_eq_norm] at hu
  obtain ⟨N, hN⟩ := eventually_exists_trial_approximation S hS hd u (half_pos hε)
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨v, hv, huv⟩ := hN k hk
  refine ⟨⟨v, hv⟩, ?_⟩
  have hb : ‖H10.value Ω hΩ u - trialValue (S k) ⟨v, hv⟩‖ ≤ ‖u - v‖ := by
    change ‖H10.value Ω hΩ u - H10.value Ω hΩ v‖ ≤ _
    rw [← map_sub]
    exact H10.norm_value_le _
  calc
    ‖f - trialValue (S k) ⟨v, hv⟩‖ =
        ‖(f - H10.value Ω hΩ u) + (H10.value Ω hΩ u - trialValue (S k) ⟨v, hv⟩)‖ :=
      congrArg norm (sub_add_sub_cancel _ _ _).symm
    _ ≤ ‖f - H10.value Ω hΩ u‖ + ‖H10.value Ω hΩ u - trialValue (S k) ⟨v, hv⟩‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hu (hb.trans_lt huv)
    _ = ε := add_halves _

/-- Actual mass projections converge strongly to arbitrary L² initial data. -/
theorem heatInitialProjection_tendsto (S : ℕ → Submodule ℝ (H10 Ω hΩ))
    [∀ k, FiniteDimensional ℝ (S k)] (hS : Monotone S)
    (hd : Dense (⋃ k, (S k : Set (H10 Ω hΩ)))) (f : DomainL2 Ω) :
    Tendsto (fun k => trialValue (S k) (heatInitialProjection (S k) f)) atTop (𝓝 f) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_exists_trial_L2approximation S hS hd f hε
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨v, hv⟩ := hN k hk
  rw [dist_eq_norm, norm_sub_rev]
  exact (heatInitialProjection_bestApproximation (S k) f v).trans_lt hv
end PDE
