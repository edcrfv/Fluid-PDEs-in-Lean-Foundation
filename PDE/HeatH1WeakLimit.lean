import PDE.HeatH1TimeTrace
import PDE.HeatUniqueness

/-!
# A physical L² trace for the heat equation with H₀¹ initial data

The finite scalar heat equation retains the H¹-projected initial value. Strong convergence
of those values and weak convergence of the state pass the equation to the limit. Combined
with the physical time equation, this constructs a heat solution with an L² physical time
derivative and a continuous physical representative attaining the initial value. Integrated
uniqueness transfers the result to every solution with that H₀¹ datum.

The physical energy identity and extension of this trace to arbitrary L² data remain separate.
-/

open InnerProductSpace MeasureTheory Set Filter
open scoped Topology
namespace PDE
variable {n : ℕ} {Ω : Set (Space n)} {hΩ : IsOpen Ω}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] trialNormedAddCommGroup trialSeminormedAddCommGroup
  trialNormedSpace trialInnerProductSpace trialDualTopology

theorem heatGalerkinVelocity_weakEquation (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (u₀ v : S) (t : ℝ) :
    inner ℝ (trialValue S v) (heatGalerkinVelocity S u₀ t) =
      -dirichletForm Ω hΩ v.val (heatGalerkin S u₀ t).val := by
  rw [real_inner_comm]
  unfold heatGalerkinVelocity massVelocity
  rw [map_neg, inner_neg_left]
  change -massForm (trialValue S)
    (massEvolutionOperator (trialValue S) (trialValue_injective S) (trialDirichletForm S)
      (massEvolution (trialValue S) (trialValue_injective S) (trialDirichletForm S) u₀ t)) v = _
  rw [massEvolutionOperator_spec, trialDirichletForm_apply, dirichletForm_symm]
  rfl
/-- The finite scalar heat equation with its actual H¹-projected initial value. -/
theorem heatH1_integrated_weakEquation (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (h : H10 Ω hΩ) (v : S) {T : ℝ} (hT : 0 ≤ T)
    (η η' : ℝ → ℝ) (hη : ∀ t, HasDerivAt η (η' t) t) (hη' : Continuous η') (hηT : η T = 0) :
    (∫ t in Icc (0 : ℝ) T, η' t * inner ℝ (H10.value Ω hΩ v.val)
      (H10.value Ω hΩ (heatH1InEnergySpace S h T t))) -
      (∫ t in Icc (0 : ℝ) T, η t * dirichletForm Ω hΩ v.val (heatH1InEnergySpace S h T t)) =
        -η 0 * inner ℝ (trialValue S (heatH1InitialProjection S h)) (H10.value Ω hΩ v.val) := by
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun t => (hη t).continuousAt
  let ℓ := innerSL ℝ (H10.value Ω hΩ v.val)
  have he := congrArg ℓ (heatH1_integrated_physical S h hT η η' hη hη' hηT)
  rw [map_add, timeL2_weighted_integral_apply (H10.value Ω hΩ) (heatH1InEnergySpace S h T) η' hη' ℓ,
    ← ℓ.integral_comp_comm (timeL2_weighted_integrable (heatH1VelocityInL2 S h T) η hηc),
    map_smul, smul_eq_mul] at he
  have hd : (∫ t in Icc (0 : ℝ) T, ℓ (η t • heatH1VelocityInL2 S h T t)) =
      -(∫ t in Icc (0 : ℝ) T, η t * dirichletForm Ω hΩ v.val (heatH1InEnergySpace S h T t)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [heatH1InEnergySpace_ae S h T, heatH1VelocityInL2_ae S h T] with t hu hd
    rw [map_smul, smul_eq_mul, hu, hd]
    change η t * inner ℝ (trialValue S v)
      (heatGalerkinVelocity S (heatH1InitialProjection S h) t) = _
    rw [heatGalerkinVelocity_weakEquation, mul_neg]
    rfl
  rw [hd] at he
  change (∫ t in Icc (0 : ℝ) T, η' t * inner ℝ (H10.value Ω hΩ v.val)
      (H10.value Ω hΩ (heatH1InEnergySpace S h T t))) +
      -(∫ t in Icc (0 : ℝ) T, η t * dirichletForm Ω hΩ v.val (heatH1InEnergySpace S h T t)) =
        (-η 0) * inner ℝ (H10.value Ω hΩ v.val) (trialValue S (heatH1InitialProjection S h)) at he
  simpa only [sub_eq_add_neg, real_inner_comm] using he
/-- The state limit solves the heat equation with the original H₀¹ datum. -/
theorem heatH1_weak_limit_solves (S : ℕ → Submodule ℝ (H10 Ω hΩ))
    [∀ k, FiniteDimensional ℝ (S k)] (hS : Monotone S)
    (hdense : Dense (⋃ k, (S k : Set (H10 Ω hΩ)))) (h : H10 Ω hΩ)
    {T : ℝ} (hT : 0 ≤ T) (u : HeatEnergySpace Ω hΩ T) (r : ℕ → ℕ) (hr : StrictMono r)
    (hu : ∀ z : HeatEnergySpace Ω hΩ T,
      Tendsto (fun k => inner ℝ (heatH1InEnergySpace (S (r k)) h T) z) atTop (𝓝 (inner ℝ u z))) :
    IsIntegratedWeakHeatSolution (H10.value Ω hΩ h) T u := by
  intro η η' hη hη' hηT v
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun t => (hη t).continuousAt
  let R := heatTimeResidual (H10.value Ω hΩ h) T u η η' hηc hη'
  have hzero : (⋃ k, (S k : Set (H10 Ω hΩ))) ⊆ {w | R w = 0} := by
    intro w hw
    obtain ⟨N, hN⟩ := mem_iUnion.mp hw
    have he : ∀ᶠ k in atTop,
        (∫ t in Icc (0 : ℝ) T, η' t * inner ℝ (H10.value Ω hΩ w)
          (H10.value Ω hΩ (heatH1InEnergySpace (S (r k)) h T t))) -
          (∫ t in Icc (0 : ℝ) T, η t * dirichletForm Ω hΩ w (heatH1InEnergySpace (S (r k)) h T t)) =
            -η 0 * inner ℝ (trialValue (S (r k)) (heatH1InitialProjection (S (r k)) h))
              (H10.value Ω hΩ w) := by
      filter_upwards [eventually_ge_atTop N] with k hk
      exact heatH1_integrated_weakEquation (S (r k)) h
        ⟨w, hS (hk.trans (hr.id_le k)) hN⟩ hT η η' hη hη' hηT
    have ha := timeL2_weighted_clm_tendsto (V := H10 Ω hΩ) η' hη'
      ((innerSL ℝ (H10.value Ω hΩ w)).comp (H10.value Ω hΩ))
      (fun k => heatH1InEnergySpace (S (r k)) h T) u hu
    have hb := timeL2_weighted_clm_tendsto (V := H10 Ω hΩ) η hηc (dirichletForm Ω hΩ w)
      (fun k => heatH1InEnergySpace (S (r k)) h T) u hu
    have hc := ((heatH1InitialProjection_value_tendsto S hS hdense h).comp hr.tendsto_atTop).inner
      (𝕜 := ℝ) (tendsto_const_nhds (x := H10.value Ω hΩ w))
    have hlim := tendsto_nhds_unique (ha.sub hb)
      ((hc.const_mul (-η 0)).congr' (Filter.EventuallyEq.symm he))
    change R w = 0
    rw [heatTimeResidual_apply]
    change (∫ t in Icc (0 : ℝ) T, η' t * inner ℝ (H10.value Ω hΩ w)
      (H10.value Ω hΩ (u t))) -
      (∫ t in Icc (0 : ℝ) T, η t * dirichletForm Ω hΩ w (u t)) =
        -η 0 * inner ℝ (H10.value Ω hΩ h) (H10.value Ω hΩ w) at hlim
    linarith
  have hz : R v = 0 :=
    (closure_minimal hzero (isClosed_eq R.continuous continuous_const)) (hdense v)
  rw [heatTimeResidual_apply] at hz
  linarith

/-- Construct a heat solution with a physical L² time derivative and continuous initial trace
for H₀¹ initial data, on any open domain in any dimension. -/
theorem exists_heatH1_solution_with_physical_trace (Ω : Set (Space n)) (hΩ : IsOpen Ω)
    (h : H10 Ω hΩ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ u : HeatEnergySpace Ω hΩ T, ∃ d : HeatVelocitySpace Ω T, ∃ q : ℝ → DomainL2 Ω,
      IsIntegratedWeakHeatSolution (H10.value Ω hΩ h) T u ∧
      HasL2TimeDerivative 0 T (heatPhysicalInTime T u) d ∧
      ContinuousOn q (Icc (0 : ℝ) T) ∧ q 0 = H10.value Ω hΩ h ∧
      (heatPhysicalInTime T u =ᵐ[volume.restrict (Icc (0 : ℝ) T)] q) ∧
      ‖u‖ ≤ Real.sqrt T * ‖h‖ ∧ ‖d‖ ≤ Real.sqrt (1 / 2) * ‖h‖ := by
  let S := initialTrialSpace (TopologicalSpace.denseSeq (H10 Ω hΩ))
  have hS : Monotone S := initialTrialSpace_mono _
  have hdense : Dense (⋃ k, (S k : Set (H10 Ω hΩ))) :=
    initialTrialSpace_dense _ (TopologicalSpace.denseRange_denseSeq (H10 Ω hΩ))
  obtain ⟨u, d, hub, hdb, r, hr, hu, hd⟩ := heatH1_exists_joint_weak_subsequence S h hT
  have hi := heatH1_weak_limit_integrated_physical S hS hdense h hT u d r hr hu hd
  have hdi : IntegrableOn (fun t => d t) (Icc (0 : ℝ) T) := (Lp.memLp d).integrable (by norm_num)
  exact ⟨u, d, timePrimitive 0 (H10.value Ω hΩ h) d,
    heatH1_weak_limit_solves S hS hdense h hT u r hr hu,
    heatPhysical_hasL2TimeDerivative_of_integrated h T u d hi,
    timePrimitive_continuousOn (H10.value Ω hΩ h) hdi,
    timePrimitive_initial 0 (H10.value Ω hΩ h) d,
    heatPhysical_ae_primitive_of_integrated h hT u d hi, hub, hdb⟩
/-- Uniqueness transfers physical time regularity to every weak solution with H₀¹ initial data. -/
theorem IsIntegratedWeakHeatSolution.physical_trace_of_H1 {h : H10 Ω hΩ} {T : ℝ}
    {u : HeatEnergySpace Ω hΩ T} (hu : IsIntegratedWeakHeatSolution (H10.value Ω hΩ h) T u)
    (hT : 0 ≤ T) :
    ∃ d : HeatVelocitySpace Ω T, ∃ q : ℝ → DomainL2 Ω,
      HasL2TimeDerivative 0 T (heatPhysicalInTime T u) d ∧
      ContinuousOn q (Icc (0 : ℝ) T) ∧ q 0 = H10.value Ω hΩ h ∧
      (heatPhysicalInTime T u =ᵐ[volume.restrict (Icc (0 : ℝ) T)] q) ∧
      ‖u‖ ≤ Real.sqrt T * ‖h‖ ∧ ‖d‖ ≤ Real.sqrt (1 / 2) * ‖h‖ := by
  obtain ⟨v, d, q, hv, hder, hcont, hinit, hae, hvb, hdb⟩ :=
    exists_heatH1_solution_with_physical_trace Ω hΩ h hT
  rw [hu.unique hv hT]
  exact ⟨d, q, hder, hcont, hinit, hae, hvb, hdb⟩
end PDE
