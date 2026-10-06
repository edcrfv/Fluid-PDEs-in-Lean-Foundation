import PDE.HeatH1Bochner
import PDE.TimeWeakLimit
import PDE.TimeIntegrationByParts

/-!
# Physical time regularity of the H¹-initialized heat limit

Pass the physical time equation to the common state/velocity weak limit, retaining the
strongly convergent initial values. The resulting physical weak time derivative reconstructs
a continuous primitive. The heat equation for that limit is verified in `HeatH1WeakLimit`.
-/

open InnerProductSpace MeasureTheory Set Filter
open scoped Topology
namespace PDE
variable {n : ℕ} {Ω : Set (Space n)} {hΩ : IsOpen Ω}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] trialNormedAddCommGroup trialSeminormedAddCommGroup
  trialNormedSpace trialInnerProductSpace trialDualTopology

/-- The physical L² value of a Bochner H₀¹ trajectory as an actual time-L² class. -/
noncomputable def heatPhysicalInTime (T : ℝ) (u : HeatEnergySpace Ω hΩ T) : HeatVelocitySpace Ω T :=
  (H10.value Ω hΩ).compLpL 2 (volume.restrict (Icc (0 : ℝ) T)) u

theorem heatPhysicalInTime_ae (T : ℝ) (u : HeatEnergySpace Ω hΩ T) :
    heatPhysicalInTime T u =ᵐ[volume.restrict (Icc (0 : ℝ) T)] (fun t => H10.value Ω hΩ (u t)) :=
  ContinuousLinearMap.coeFn_compLpL _ _

/-- The finite physical time equation retains the actual H¹-projected initial datum. -/
theorem heatH1_integrated_physical (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (h : H10 Ω hΩ) {T : ℝ} (hT : 0 ≤ T)
    (η η' : ℝ → ℝ) (hη : ∀ t, HasDerivAt η (η' t) t) (hη' : Continuous η') (hηT : η T = 0) :
    (∫ t in Icc (0 : ℝ) T, η' t • H10.value Ω hΩ (heatH1InEnergySpace S h T t)) +
      (∫ t in Icc (0 : ℝ) T, η t • heatH1VelocityInL2 S h T t) =
        (-η 0) • trialValue S (heatH1InitialProjection S h) := by
  have he := time_integrated_initial_of_hasDerivAt
    (fun t => H10.value Ω hΩ (heatH1Trajectory S h t)) (heatH1Velocity S h)
    (heatH1Velocity_hasDerivAt S h) (heatH1Velocity_continuous S h) η η' hη hη' hT hηT
  rw [heatH1Trajectory_zero] at he
  have h₁ : (∫ t in Icc (0 : ℝ) T, η' t • H10.value Ω hΩ (heatH1InEnergySpace S h T t)) =
      ∫ t in Icc (0 : ℝ) T, η' t • H10.value Ω hΩ (heatH1Trajectory S h t) := by
    apply integral_congr_ae
    filter_upwards [heatH1InEnergySpace_ae S h T] with t ht
    rw [ht]
  have h₂ : (∫ t in Icc (0 : ℝ) T, η t • heatH1VelocityInL2 S h T t) =
      ∫ t in Icc (0 : ℝ) T, η t • heatH1Velocity S h t := by
    apply integral_congr_ae
    filter_upwards [heatH1VelocityInL2_ae S h T] with t ht
    rw [ht]
  rw [h₁, h₂]
  exact he

/-- The physical time equation passes to the common weak state/velocity limit. -/
theorem heatH1_weak_limit_integrated_physical (S : ℕ → Submodule ℝ (H10 Ω hΩ))
    [∀ k, FiniteDimensional ℝ (S k)] (hS : Monotone S)
    (hdense : Dense (⋃ k, (S k : Set (H10 Ω hΩ)))) (h : H10 Ω hΩ)
    {T : ℝ} (hT : 0 ≤ T) (u : HeatEnergySpace Ω hΩ T) (d : HeatVelocitySpace Ω T)
    (r : ℕ → ℕ) (hr : StrictMono r)
    (hu : ∀ z : HeatEnergySpace Ω hΩ T,
      Tendsto (fun k => inner ℝ (heatH1InEnergySpace (S (r k)) h T) z) atTop (𝓝 (inner ℝ u z)))
    (hd : ∀ z : HeatVelocitySpace Ω T,
      Tendsto (fun k => inner ℝ (heatH1VelocityInL2 (S (r k)) h T) z) atTop (𝓝 (inner ℝ d z)))
    (η η' : ℝ → ℝ) (hη : ∀ t, HasDerivAt η (η' t) t) (hη' : Continuous η') (hηT : η T = 0) :
    (∫ t in Icc (0 : ℝ) T, η' t • H10.value Ω hΩ (u t)) +
      (∫ t in Icc (0 : ℝ) T, η t • d t) = (-η 0) • H10.value Ω hΩ h := by
  simpa only using! (integrated_time_equation_of_weak_limits
    (a := 0) (b := T) (V := H10 Ω hΩ) (H := DomainL2 Ω)
    (H10.value Ω hΩ) (fun k => heatH1InEnergySpace (S (r k)) h T)
    (fun k => heatH1VelocityInL2 (S (r k)) h T)
    (fun k => trialValue (S (r k)) (heatH1InitialProjection (S (r k)) h)) u d (H10.value Ω hΩ h)
    hu hd ((heatH1InitialProjection_value_tendsto S hS hdense h).comp hr.tendsto_atTop)
    (fun k ψ ψ' hψ hψ' hψT => by
      simpa only using! heatH1_integrated_physical (S (r k)) h hT ψ ψ' hψ hψ' hψT)
    η η' hη hη' hηT)

/-- The integrated physical equation identifies the continuous primitive as an a.e. representative. -/
theorem heatPhysical_ae_primitive_of_integrated (h : H10 Ω hΩ) {T : ℝ} (hT : 0 ≤ T)
    (u : HeatEnergySpace Ω hΩ T) (d : HeatVelocitySpace Ω T)
    (hi : ∀ (η η' : ℝ → ℝ), (∀ t, HasDerivAt η (η' t) t) → Continuous η' → η T = 0 →
      (∫ t in Icc (0 : ℝ) T, η' t • H10.value Ω hΩ (u t)) +
        (∫ t in Icc (0 : ℝ) T, η t • d t) = (-η 0) • H10.value Ω hΩ h) :
    heatPhysicalInTime T u =ᵐ[volume.restrict (Icc (0 : ℝ) T)]
      timePrimitive 0 (H10.value Ω hΩ h) d := by
  apply ae_eq_timePrimitive_of_integrated hT (H10.value Ω hΩ h) (heatPhysicalInTime T u) d
  intro η η' hη hη' hηT
  have he : (∫ t in Icc (0 : ℝ) T, η' t • heatPhysicalInTime T u t) =
      ∫ t in Icc (0 : ℝ) T, η' t • H10.value Ω hΩ (u t) := by
    apply integral_congr_ae
    filter_upwards [heatPhysicalInTime_ae T u] with t ht
    rw [ht]
  rw [he]
  exact hi η η' hη hη' hηT

/-- In the physical L² space, the common velocity limit is the weak time derivative. -/
theorem heatPhysical_hasL2TimeDerivative_of_integrated (h : H10 Ω hΩ) (T : ℝ)
    (u : HeatEnergySpace Ω hΩ T) (d : HeatVelocitySpace Ω T)
    (hi : ∀ (η η' : ℝ → ℝ), (∀ t, HasDerivAt η (η' t) t) → Continuous η' → η T = 0 →
      (∫ t in Icc (0 : ℝ) T, η' t • H10.value Ω hΩ (u t)) +
        (∫ t in Icc (0 : ℝ) T, η t • d t) = (-η 0) • H10.value Ω hΩ h) :
    HasL2TimeDerivative 0 T (heatPhysicalInTime T u) d := by
  intro η η' hη hη' hη0 hηT
  have he := hi η η' hη hη' hηT
  have hp : (∫ t in Icc (0 : ℝ) T, η' t • heatPhysicalInTime T u t) =
      ∫ t in Icc (0 : ℝ) T, η' t • H10.value Ω hΩ (u t) := by
    apply integral_congr_ae
    filter_upwards [heatPhysicalInTime_ae T u] with t ht
    rw [ht]
  rw [← hp, hη0, neg_zero, zero_smul] at he
  exact eq_neg_of_add_eq_zero_left he
end PDE
