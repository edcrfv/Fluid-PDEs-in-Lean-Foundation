import PDE.HeatWeakLimit
import PDE.WeakTimeDerivative

/-!
# The heat time derivative in the dual energy space

The mass trajectory J*J u and the candidate derivative -B u are actual L² functions
with values in (H₀¹)*. The scalar integrated equation gives a Bochner identity with
the initial datum in that dual. In particular, it proves weak time differentiation
and an L² norm bound for the derivative. Time traces and the continuous L² representative
remain separate results.

The local dual instances spell out the inherited operator norm and topology, as in
the finite trial-space construction; they introduce no alternative mathematical structure.
-/

open MeasureTheory InnerProductSpace Set
namespace PDE
variable {n : ℕ} {Ω : Set (Space n)} {hΩ : IsOpen Ω}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable local instance heatDualNormedAddCommGroup : NormedAddCommGroup (H10 Ω hΩ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ) (E := H10 Ω hΩ) (F := ℝ)
noncomputable local instance heatDualSeminormedAddCommGroup : SeminormedAddCommGroup (H10 Ω hΩ →L[ℝ] ℝ) :=
  (heatDualNormedAddCommGroup (Ω := Ω) (hΩ := hΩ)).toSeminormedAddCommGroup
noncomputable local instance heatDualNormedSpace : NormedSpace ℝ (H10 Ω hΩ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
noncomputable local instance heatDualTopology : TopologicalSpace (H10 Ω hΩ →L[ℝ] ℝ) :=
  ContinuousLinearMap.topologicalSpace (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
    (E := H10 Ω hΩ) (F := ℝ)

/-- The L² mass trajectory as a function with values in the dual energy space. -/
noncomputable def heatMassInTime (T : ℝ) (u : HeatEnergySpace Ω hΩ T) :
    TimeL2 (H10 Ω hΩ →L[ℝ] ℝ) 0 T :=
  (heatMassForm Ω hΩ).compLpL 2 (volume.restrict (Icc (0 : ℝ) T)) u

/-- The candidate time derivative in the dual energy space: minus the Dirichlet form. -/
noncomputable def heatDualDerivative (T : ℝ) (u : HeatEnergySpace Ω hΩ T) :
    TimeL2 (H10 Ω hΩ →L[ℝ] ℝ) 0 T :=
  (-dirichletForm Ω hΩ).compLpL 2 (volume.restrict (Icc (0 : ℝ) T)) u

theorem heatMassInTime_ae (T : ℝ) (u : HeatEnergySpace Ω hΩ T) :
    heatMassInTime T u =ᵐ[volume.restrict (Icc (0 : ℝ) T)] (fun t => heatMassForm Ω hΩ (u t)) :=
  ContinuousLinearMap.coeFn_compLpL _ _

theorem heatDualDerivative_ae (T : ℝ) (u : HeatEnergySpace Ω hΩ T) :
    heatDualDerivative T u =ᵐ[volume.restrict (Icc (0 : ℝ) T)]
      (fun t => -dirichletForm Ω hΩ (u t)) :=
  ContinuousLinearMap.coeFn_compLpL _ _

theorem heatDualDerivative_norm_le (T : ℝ) (u : HeatEnergySpace Ω hΩ T) :
    ‖heatDualDerivative T u‖ ≤ ‖dirichletForm Ω hΩ‖ * ‖u‖ := by
  unfold heatDualDerivative
  change ‖(-dirichletForm Ω hΩ).compLp u‖ ≤ _
  simpa only [norm_neg] using (-dirichletForm Ω hΩ).norm_compLp_le u

/-- The scalar weak equation gives an actual Bochner identity in the dual energy space. -/
theorem IsIntegratedWeakHeatSolution.dual_integrated {f : DomainL2 Ω} {T : ℝ}
    {u : HeatEnergySpace Ω hΩ T} (hu : IsIntegratedWeakHeatSolution f T u)
    (η η' : ℝ → ℝ) (hη : ∀ t, HasDerivAt η (η' t) t) (hη' : Continuous η') (hηT : η T = 0) :
    (∫ t in Icc (0 : ℝ) T, η' t • heatMassInTime T u t) +
      (∫ t in Icc (0 : ℝ) T, η t • heatDualDerivative T u t) =
        (-η 0) • poissonLoad Ω hΩ f := by
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun t => (hη t).continuousAt
  have hm := timeL2_weighted_integrable (heatMassInTime T u) η' hη'
  have hd := timeL2_weighted_integrable (heatDualDerivative T u) η hηc
  apply ContinuousLinearMap.ext
  intro v
  rw [add_apply, ContinuousLinearMap.integral_apply hm v,
    ContinuousLinearMap.integral_apply hd v]
  have hi₁ : (∫ t in Icc (0 : ℝ) T, (η' t • heatMassInTime T u t) v) =
      ∫ t in Icc (0 : ℝ) T, η' t * inner ℝ (H10.value Ω hΩ v) (H10.value Ω hΩ (u t)) := by
    apply integral_congr_ae
    filter_upwards [heatMassInTime_ae T u] with t ht
    simp only [smul_apply, ht, heatMassForm_apply, smul_eq_mul]
    rw [real_inner_comm]
  have hi₂ : (∫ t in Icc (0 : ℝ) T, (η t • heatDualDerivative T u t) v) =
      -(∫ t in Icc (0 : ℝ) T, η t * dirichletForm Ω hΩ v (u t)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [heatDualDerivative_ae T u] with t ht
    simp only [smul_apply, ht, neg_apply,
      smul_eq_mul, mul_neg]
    rw [dirichletForm_symm]
  rw [hi₁, hi₂]
  exact hu η η' hη hη' hηT v

/-- The mass trajectory has an L² weak time derivative in (H₀¹)*. -/
theorem IsIntegratedWeakHeatSolution.hasL2TimeDerivative {f : DomainL2 Ω} {T : ℝ}
    {u : HeatEnergySpace Ω hΩ T} (hu : IsIntegratedWeakHeatSolution f T u) :
    HasL2TimeDerivative 0 T (heatMassInTime T u) (heatDualDerivative T u) := by
  intro η η' hη hη' hη0 hηT
  have hi := hu.dual_integrated η η' hη hη' hηT
  rw [hη0, neg_zero, zero_smul] at hi
  exact eq_neg_of_add_eq_zero_left hi
end PDE
