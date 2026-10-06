import PDE.HeatDualTrace
import PDE.PrimitiveEnergy

/-!
# Uniqueness of the integrated weak heat solution

The continuous dual representative identifies the mass map of a zero-initial solution
with minus the Dirichlet form applied to its time primitive. This gives nonpositive
physical energy production for that primitive. Absolute continuity and Lebesgue
differentiation force the primitive, then the solution, to vanish. Subtraction yields
uniqueness, and the constructed solution supplies the energy bound for every solution.
No continuous representative in physical L² is assumed in this argument.
-/

open MeasureTheory InnerProductSpace Set
namespace PDE
variable {n : ℕ} {Ω : Set (Space n)} {hΩ : IsOpen Ω}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] heatDualNormedAddCommGroup heatDualSeminormedAddCommGroup
  heatDualNormedSpace heatDualTopology

theorem IsIntegratedWeakHeatSolution.sub {f g : DomainL2 Ω} {T : ℝ}
    {u v : HeatEnergySpace Ω hΩ T} (hu : IsIntegratedWeakHeatSolution f T u)
    (hv : IsIntegratedWeakHeatSolution g T v) : IsIntegratedWeakHeatSolution (f - g) T (u - v) := by
  intro η η' hη hη' hηT w
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun t => (hη t).continuousAt
  have hm : (∫ t in Icc (0 : ℝ) T, η' t * inner ℝ (H10.value Ω hΩ w)
      (H10.value Ω hΩ ((u - v) t))) =
      (∫ t in Icc (0 : ℝ) T, η' t * inner ℝ (H10.value Ω hΩ w) (H10.value Ω hΩ (u t))) -
      (∫ t in Icc (0 : ℝ) T, η' t * inner ℝ (H10.value Ω hΩ w) (H10.value Ω hΩ (v t))) := by
    rw [← integral_sub (heatTimeIntegrands_integrable T u η' hη' w).1
      (heatTimeIntegrands_integrable T v η' hη' w).1]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub u v] with t ht
    rw [ht, Pi.sub_apply, map_sub, inner_sub_right, mul_sub]
  have hb : (∫ t in Icc (0 : ℝ) T, η t * dirichletForm Ω hΩ w ((u - v) t)) =
      (∫ t in Icc (0 : ℝ) T, η t * dirichletForm Ω hΩ w (u t)) -
      (∫ t in Icc (0 : ℝ) T, η t * dirichletForm Ω hΩ w (v t)) := by
    rw [← integral_sub (heatTimeIntegrands_integrable T u η hηc w).2
      (heatTimeIntegrands_integrable T v η hηc w).2]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub u v] with t ht
    rw [ht, Pi.sub_apply, map_sub, mul_sub]
  rw [hm, hb, inner_sub_left, mul_sub]
  linarith [hu η η' hη hη' hηT w, hv η η' hη hη' hηT w]
/-- Zero initial data force the integrated heat solution to vanish, by testing the
physical energy of its time primitive. -/
theorem IsIntegratedWeakHeatSolution.eq_zero {T : ℝ} {u : HeatEnergySpace Ω hΩ T}
    (hu : IsIntegratedWeakHeatSolution (0 : DomainL2 Ω) T u) (hT : 0 ≤ T) : u = 0 := by
  apply timeL2_eq_zero_of_primitive_energy (V := H10 Ω hΩ) hT u
    (H10.value Ω hΩ) (H10.value_injective Ω hΩ)
  have hload : poissonLoad Ω hΩ (0 : DomainL2 Ω) = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    change inner ℝ (0 : DomainL2 Ω) (H10.value Ω hΩ v) = 0
    exact inner_zero_left _
  filter_upwards [hu.dualRepresentative_ae hT, ae_restrict_mem measurableSet_Icc] with t ht htmem
  have hP : (∫ s in Icc (0 : ℝ) t, u s) = ∫ s in (0 : ℝ)..t, u s := by
    rw [intervalIntegral.integral_of_le htmem.1, integral_Icc_eq_integral_Ioc]
  rw [heatDualRepresentative_eq _ _ _ htmem, hload, zero_sub, hP] at ht
  let P : H10 Ω hΩ := ∫ s in (0 : ℝ)..t, u s
  have hp := congrArg (fun ℓ : H10 Ω hΩ →L[ℝ] ℝ => ℓ P) ht
  change inner ℝ (H10.value Ω hΩ (u t)) (H10.value Ω hΩ P) = -dirichletForm Ω hΩ P P at hp
  rw [real_inner_comm] at hp
  have hB : 0 ≤ dirichletForm Ω hΩ P P := by
    rw [dirichletForm_self]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  exact hp.le.trans (neg_nonpos.mpr hB)

/-- Uniqueness in the actual Bochner energy space for the time-integrated heat equation. -/
theorem IsIntegratedWeakHeatSolution.unique {f : DomainL2 Ω} {T : ℝ}
    {u v : HeatEnergySpace Ω hΩ T} (hu : IsIntegratedWeakHeatSolution f T u)
    (hv : IsIntegratedWeakHeatSolution f T v) (hT : 0 ≤ T) : u = v := by
  have hs : IsIntegratedWeakHeatSolution (0 : DomainL2 Ω) T (u - v) := by
    simpa only [sub_self] using hu.sub hv
  exact sub_eq_zero.mp (hs.eq_zero hT)

/-- Concrete existence and uniqueness of an integrated weak heat solution on any open domain. -/
theorem exists_unique_integrated_weakHeatSolution (Ω : Set (Space n)) (hΩ : IsOpen Ω)
    (f : DomainL2 Ω) {T : ℝ} (hT : 0 ≤ T) :
    ∃! u : HeatEnergySpace Ω hΩ T, IsIntegratedWeakHeatSolution f T u := by
  obtain ⟨u, hu, _⟩ := exists_integrated_weakHeatSolution Ω hΩ f hT
  exact ⟨u, hu, fun v hv => hv.unique hu hT⟩

/-- Every integrated weak heat solution has the proved Bochner energy bound. -/
theorem IsIntegratedWeakHeatSolution.norm_le {f : DomainL2 Ω} {T : ℝ}
    {u : HeatEnergySpace Ω hΩ T} (hu : IsIntegratedWeakHeatSolution f T u) (hT : 0 ≤ T) :
    ‖u‖ ≤ Real.sqrt (T + 1 / 2) * ‖f‖ := by
  obtain ⟨v, hv, hb⟩ := exists_integrated_weakHeatSolution Ω hΩ f hT
  rwa [hu.unique hv hT]
end PDE
