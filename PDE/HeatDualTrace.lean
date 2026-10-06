import PDE.HeatTimeDerivative
import PDE.TimePrimitive

/-!
# Continuous time trace in the dual energy space

The initial L² datum and the integral of the proved dual derivative construct a
continuous representative in (H₀¹)*. The integrated heat equation identifies it
almost everywhere with the L² mass trajectory and gives its initial value exactly.
This proves a dual-space trace; a continuous representative in physical L² remains
a separate, stronger target.
-/

open MeasureTheory InnerProductSpace Set
namespace PDE
variable {n : ℕ} {Ω : Set (Space n)} {hΩ : IsOpen Ω}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] heatDualNormedAddCommGroup heatDualSeminormedAddCommGroup
  heatDualNormedSpace heatDualTopology

/-- The continuous representative of the heat mass trajectory in (H₀¹)*. -/
noncomputable def heatDualRepresentative (f : DomainL2 Ω) (T : ℝ)
    (u : HeatEnergySpace Ω hΩ T) : ℝ → H10 Ω hΩ →L[ℝ] ℝ :=
  timePrimitive 0 (poissonLoad Ω hΩ f) (heatDualDerivative T u)

theorem heatDualRepresentative_initial (f : DomainL2 Ω) (T : ℝ)
    (u : HeatEnergySpace Ω hΩ T) : heatDualRepresentative f T u 0 = poissonLoad Ω hΩ f :=
  timePrimitive_initial _ _ _

theorem heatDualRepresentative_continuousOn (f : DomainL2 Ω) (T : ℝ)
    (u : HeatEnergySpace Ω hΩ T) : ContinuousOn (heatDualRepresentative f T u) (Icc (0 : ℝ) T) :=
  timePrimitive_continuousOn _ ((Lp.memLp (heatDualDerivative T u)).integrable (by norm_num))

/-- The continuous dual representative agrees almost everywhere with the actual heat mass map. -/
theorem IsIntegratedWeakHeatSolution.dualRepresentative_ae {f : DomainL2 Ω} {T : ℝ}
    {u : HeatEnergySpace Ω hΩ T} (hu : IsIntegratedWeakHeatSolution f T u) (hT : 0 ≤ T) :
    (fun t => heatMassForm Ω hΩ (u t)) =ᵐ[volume.restrict (Icc (0 : ℝ) T)]
      heatDualRepresentative f T u := by
  have he := ae_eq_timePrimitive_of_integrated (E := H10 Ω hΩ →L[ℝ] ℝ) hT
    (poissonLoad Ω hΩ f) (heatMassInTime T u) (heatDualDerivative T u)
    (fun η η' hη hη' hηT => hu.dual_integrated η η' hη hη' hηT)
  exact (heatMassInTime_ae T u).symm.trans he

/-- The dual-valued primitive has an explicit form in terms of the H₀¹ integral of u. -/
theorem heatDualRepresentative_eq (f : DomainL2 Ω) (T : ℝ)
    (u : HeatEnergySpace Ω hΩ T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    heatDualRepresentative f T u t = poissonLoad Ω hΩ f -
      dirichletForm Ω hΩ (∫ s in Icc (0 : ℝ) t, u s) := by
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right ht.2
  have huI : IntegrableOn (fun s => u s) (Icc (0 : ℝ) T) := (Lp.memLp u).integrable (by norm_num)
  have hi : IntegrableOn (fun s => u s) (Icc (0 : ℝ) t) := huI.mono_set hsub
  have he : (∫ s in Icc (0 : ℝ) t, heatDualDerivative T u s) =
      ∫ s in Icc (0 : ℝ) t, -dirichletForm Ω hΩ (u s) :=
    integral_congr_ae ((heatDualDerivative_ae T u).filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
  unfold heatDualRepresentative timePrimitive
  rw [he, integral_neg, (dirichletForm Ω hΩ).integral_comp_comm hi]
  rfl
end PDE
