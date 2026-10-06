import PDE.HeatWeakForm
import PDE.HeatIntegratedGalerkin

/-!
# Constructing an integrated weak heat solution

Finite heat trajectories have a weakly convergent subsequence in L²(0,T;H₀¹).
Each fixed spatial trial test is admissible eventually, so weak convergence passes
through the mass and stiffness time integrals. Continuity of the residual and density
extend the equation to every H₀¹ test. The initial mass projection contributes exactly
the original L² datum. Continuous L² representatives, time traces and infinite-dimensional
uniqueness remain separate obligations.
-/

open InnerProductSpace MeasureTheory Set Filter
open scoped Topology ENNReal
namespace PDE
variable {n : ℕ} {Ω : Set (Space n)} {hΩ : IsOpen Ω}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] trialNormedAddCommGroup trialSeminormedAddCommGroup
  trialNormedSpace trialInnerProductSpace trialDualTopology

/-- Each finite-dimensional residual vanishes on its trial space. -/
theorem heatTimeResidual_galerkin_eq_zero (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (f : DomainL2 Ω) (η η' : ℝ → ℝ)
    (hη : ∀ t, HasDerivAt η (η' t) t) (hηc : Continuous η) (hη' : Continuous η')
    {T : ℝ} (hT : 0 ≤ T) (hηT : η T = 0) (v : H10 Ω hΩ) (hv : v ∈ S) :
    heatTimeResidual f T (heatGalerkinInEnergySpace S f T) η η' hηc hη' v = 0 := by
  rw [heatTimeResidual_apply]
  have hi₁ : (∫ t in Icc (0 : ℝ) T, η' t * inner ℝ (H10.value Ω hΩ v)
      (H10.value Ω hΩ (heatGalerkinInEnergySpace S f T t))) =
      ∫ t in Icc (0 : ℝ) T, η' t * inner ℝ (H10.value Ω hΩ v)
        (H10.value Ω hΩ (heatTrajectory S f t)) := by
    apply integral_congr_ae
    filter_upwards [heatGalerkinInEnergySpace_ae S f T] with t ht
    rw [ht]
  have hi₂ : (∫ t in Icc (0 : ℝ) T, η t * dirichletForm Ω hΩ v
      (heatGalerkinInEnergySpace S f T t)) =
      ∫ t in Icc (0 : ℝ) T, η t * dirichletForm Ω hΩ v (heatTrajectory S f t) := by
    apply integral_congr_ae
    filter_upwards [heatGalerkinInEnergySpace_ae S f T] with t ht
    rw [ht]
  rw [hi₁, hi₂]
  have he := heatGalerkin_integrated_weakEquation S f ⟨v, hv⟩ η η' hη hη' hηT
  simp only [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc] at he
  linarith

/-- Weak Bochner convergence passes through every fixed time residual. -/
theorem heatTimeResidual_tendsto (f : DomainL2 Ω) (T : ℝ)
    (u : ℕ → HeatEnergySpace Ω hΩ T) (w : HeatEnergySpace Ω hΩ T)
    (hu : ∀ z : HeatEnergySpace Ω hΩ T,
      Tendsto (fun k => inner ℝ (u k) z) atTop (𝓝 (inner ℝ w z)))
    (η η' : ℝ → ℝ) (hη : Continuous η) (hη' : Continuous η') (v : H10 Ω hΩ) :
    Tendsto (fun k => heatTimeResidual f T (u k) η η' hη hη' v) atTop
      (𝓝 (heatTimeResidual f T w η η' hη hη' v)) := by
  have h₁ := weightedTimeForm_tendsto (V := H10 Ω hΩ) (continuousTimeL2 η' hη' T)
    (heatMassForm Ω hΩ) v u w hu
  have h₂ := weightedTimeForm_tendsto (V := H10 Ω hΩ) (continuousTimeL2 η hη T)
    (dirichletForm Ω hΩ) v u w hu
  exact (h₁.sub h₂).add tendsto_const_nhds

/-- A weak limit of nested, dense heat trial spaces satisfies the integrated equation,
including the original L² initial datum. -/
theorem heat_weak_limit_solves (S : ℕ → Submodule ℝ (H10 Ω hΩ))
    [∀ k, FiniteDimensional ℝ (S k)] (hS : Monotone S)
    (hd : Dense (⋃ k, (S k : Set (H10 Ω hΩ)))) (f : DomainL2 Ω)
    {T : ℝ} (hT : 0 ≤ T) (u : HeatEnergySpace Ω hΩ T) (r : ℕ → ℕ) (hr : StrictMono r)
    (hu : ∀ z : HeatEnergySpace Ω hΩ T,
      Tendsto (fun k => inner ℝ (heatGalerkinInEnergySpace (S (r k)) f T) z)
        atTop (𝓝 (inner ℝ u z))) : IsIntegratedWeakHeatSolution f T u := by
  intro η η' hη hη' hηT v
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun t => (hη t).continuousAt
  let R := heatTimeResidual f T u η η' hηc hη'
  have hzero : (⋃ k, (S k : Set (H10 Ω hΩ))) ⊆ {w | R w = 0} := by
    intro w hw
    obtain ⟨N, hN⟩ := mem_iUnion.mp hw
    have he : ∀ᶠ k in atTop,
        heatTimeResidual f T (heatGalerkinInEnergySpace (S (r k)) f T) η η' hηc hη' w = 0 := by
      filter_upwards [eventually_ge_atTop N] with k hk
      exact heatTimeResidual_galerkin_eq_zero (S (r k)) f η η' hη hηc hη' hT hηT w
        (hS (hk.trans (hr.id_le k)) hN)
    have hlim := heatTimeResidual_tendsto f T
      (fun k => heatGalerkinInEnergySpace (S (r k)) f T) u hu η η' hηc hη' w
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he))
  have hz : R v = 0 := (closure_minimal hzero (isClosed_eq R.continuous continuous_const)) (hd v)
  rw [heatTimeResidual_apply] at hz
  linarith

/-- Construct an energy-space solution of the time-integrated homogeneous heat equation
on any open domain, from arbitrary L² initial data. The L² time trace is a separate theorem. -/
theorem exists_integrated_weakHeatSolution (Ω : Set (Space n)) (hΩ : IsOpen Ω)
    (f : DomainL2 Ω) {T : ℝ} (hT : 0 ≤ T) :
    ∃ u : HeatEnergySpace Ω hΩ T, IsIntegratedWeakHeatSolution f T u ∧
      ‖u‖ ≤ Real.sqrt (T + 1 / 2) * ‖f‖ := by
  let S := initialTrialSpace (TopologicalSpace.denseSeq (H10 Ω hΩ))
  obtain ⟨u, hbound, r, hr, hu⟩ := heatGalerkin_exists_weak_subsequence S f hT
  refine ⟨u, ?_, hbound⟩
  exact heat_weak_limit_solves S (initialTrialSpace_mono _)
    (initialTrialSpace_dense _ (TopologicalSpace.denseRange_denseSeq (H10 Ω hΩ))) f hT u r hr hu
end PDE
