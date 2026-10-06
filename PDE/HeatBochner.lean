import PDE.HeatInitialData
import PDE.SobolevCompactness
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Heat approximations in the Bochner energy space

The actual continuous finite trajectories define L²(0,T;H₀¹) a.e. classes. The full
H¹ norm splits into the L² mass and Dirichlet energy, giving the uniform squared bound
(T + 1/2) ‖f‖². This holds on any open domain in any dimension. Separable Hilbert
weak compactness supplies a subsequence in this space. A weak equation for the limit
requires a separate passage-to-the-limit argument.
-/

open InnerProductSpace MeasureTheory Set Filter
open scoped Topology ENNReal
namespace PDE
variable {n : ℕ} {Ω : Set (Space n)} {hΩ : IsOpen Ω}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] trialNormedAddCommGroup trialSeminormedAddCommGroup
  trialNormedSpace trialInnerProductSpace trialDualTopology

theorem heatGalerkin_continuous (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (u₀ : S) : Continuous (heatGalerkin S u₀) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  unfold heatGalerkin
  exact (massEvolution_hasDerivAt (V := S) (trialValue S) (trialValue_injective S)
    (trialDirichletForm S) u₀ t).continuousAt

noncomputable def heatTrajectory (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (f : DomainL2 Ω) (t : ℝ) : H10 Ω hΩ := (heatGalerkinFromL2 S f t).val

theorem heatTrajectory_continuous (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (f : DomainL2 Ω) : Continuous (heatTrajectory S f) :=
  S.subtypeL.continuous.comp (heatGalerkin_continuous S _)

theorem H10.norm_sq_eq_value_add_dirichlet (u : H10 Ω hΩ) :
    ‖u‖ ^ 2 = ‖H10.value Ω hΩ u‖ ^ 2 + dirichletForm Ω hΩ u u := by
  rw [dirichletForm_self]
  exact H1.norm_sq_eq u.val

/-- Full H¹ energy in time, requiring no Poincaré inequality or dimension restriction. -/
theorem heatTrajectory_integrated_norm_sq_le (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (f : DomainL2 Ω) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖heatTrajectory S f t‖ ^ 2) ≤ (T + 1 / 2) * ‖f‖ ^ 2 := by
  have hu := heatTrajectory_continuous S f
  have hm : Continuous (fun t => ‖H10.value Ω hΩ (heatTrajectory S f t)‖ ^ 2) :=
    ((H10.value Ω hΩ).continuous.comp hu).norm.pow 2
  have hd : Continuous (fun t => dirichletForm Ω hΩ (heatTrajectory S f t) (heatTrajectory S f t)) :=
    ((dirichletForm Ω hΩ).continuous.comp hu).clm_apply hu
  have hb : (∫ t in (0 : ℝ)..T, ‖H10.value Ω hΩ (heatTrajectory S f t)‖ ^ 2) ≤ T * ‖f‖ ^ 2 := by
    have hp := intervalIntegral.integral_mono_on (μ := volume) hT (hm.intervalIntegrable 0 T)
      (continuous_const.intervalIntegrable 0 T) (fun t ht =>
        pow_le_pow_left₀ (norm_nonneg _) (heatGalerkinFromL2_norm_le S f ht.1) 2)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hp
  simp_rw [H10.norm_sq_eq_value_add_dirichlet]
  rw [intervalIntegral.integral_add (hm.intervalIntegrable 0 T) (hd.intervalIntegrable 0 T)]
  have he := heatGalerkinFromL2_integrated_energy_le S f T
  change (∫ t in (0 : ℝ)..T, ‖H10.value Ω hΩ (heatTrajectory S f t)‖ ^ 2) +
      (∫ t in (0 : ℝ)..T, dirichletForm Ω hΩ (heatTrajectory S f t) (heatTrajectory S f t)) ≤ _
  change (∫ t in (0 : ℝ)..T, dirichletForm Ω hΩ (heatTrajectory S f t) (heatTrajectory S f t)) ≤ _ at he
  nlinarith

/-- The Bochner L² space of zero-boundary H¹ values over a finite time interval. -/
noncomputable abbrev HeatEnergySpace (Ω : Set (Space n)) (hΩ : IsOpen Ω) (T : ℝ) :=
  Lp (H10 Ω hΩ) 2 (volume.restrict (Icc (0 : ℝ) T))

instance heatEnergySecondCountable (Ω : Set (Space n)) (hΩ : IsOpen Ω) (T : ℝ) :
    SecondCountableTopology (HeatEnergySpace Ω hΩ T) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  exact inferInstanceAs (SecondCountableTopology (Lp (H10 Ω hΩ) 2 (volume.restrict (Icc (0 : ℝ) T))))

theorem heatTrajectory_memLp (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (f : DomainL2 Ω) (T : ℝ) : MemLp (heatTrajectory S f) 2 (volume.restrict (Icc (0 : ℝ) T)) := by
  have hu := heatTrajectory_continuous S f
  exact (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mpr
    ((hu.norm.pow 2).integrableOn_Icc)

noncomputable def heatGalerkinInEnergySpace (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (f : DomainL2 Ω) (T : ℝ) : HeatEnergySpace Ω hΩ T :=
  (heatTrajectory_memLp S f T).toLp (heatTrajectory S f)

theorem heatGalerkinInEnergySpace_ae (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (f : DomainL2 Ω) (T : ℝ) :
    heatGalerkinInEnergySpace S f T =ᵐ[volume.restrict (Icc (0 : ℝ) T)] heatTrajectory S f :=
  MemLp.coeFn_toLp _

theorem heatGalerkinInEnergySpace_norm_sq_le (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (f : DomainL2 Ω) {T : ℝ} (hT : 0 ≤ T) :
    ‖heatGalerkinInEnergySpace S f T‖ ^ 2 ≤ (T + 1 / 2) * ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have hi : (∫ t in Icc (0 : ℝ) T,
      inner ℝ (heatGalerkinInEnergySpace S f T t) (heatGalerkinInEnergySpace S f T t)) =
      ∫ t in Icc (0 : ℝ) T, ‖heatTrajectory S f t‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [heatGalerkinInEnergySpace_ae S f T] with t ht
    rw [ht, real_inner_self_eq_norm_sq]
  rw [hi, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
  exact heatTrajectory_integrated_norm_sq_le S f hT

/-- Every sequence of finite heat approximations has a weak subsequence in L²(0,T;H₀¹). -/
theorem heatGalerkin_exists_weak_subsequence (S : ℕ → Submodule ℝ (H10 Ω hΩ))
    [∀ k, FiniteDimensional ℝ (S k)] (f : DomainL2 Ω) {T : ℝ} (hT : 0 ≤ T) :
    ∃ u : HeatEnergySpace Ω hΩ T, ‖u‖ ≤ Real.sqrt (T + 1 / 2) * ‖f‖ ∧
      ∃ r : ℕ → ℕ, StrictMono r ∧ ∀ w : HeatEnergySpace Ω hΩ T,
        Tendsto (fun k => inner ℝ (heatGalerkinInEnergySpace (S (r k)) f T) w)
          atTop (𝓝 (inner ℝ u w)) := by
  apply PDE.exists_weakly_convergent_subsequence (V := HeatEnergySpace Ω hΩ T)
    (fun k => heatGalerkinInEnergySpace (S k) f T)
  intro k
  have he := heatGalerkinInEnergySpace_norm_sq_le (S k) f hT
  have hs : (Real.sqrt (T + 1 / 2)) ^ 2 = T + 1 / 2 := Real.sq_sqrt (by linarith)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg f))).mp
  rwa [mul_pow, hs]
end PDE
