import PDE.HeatH1InitialData

/-!
# Simultaneous weak compactness for H¹-initialized heat trajectories

The state and its physical time derivative give bounded Bochner L² sequences. Two successive
Hilbert weak extractions produce one common subsequence, retaining both bounds. Identification
of its velocity limit as a physical weak derivative is a subsequent obligation.
-/

open InnerProductSpace MeasureTheory Set Filter
open scoped Topology ENNReal
namespace PDE
variable {n : ℕ} {Ω : Set (Space n)} {hΩ : IsOpen Ω}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] trialNormedAddCommGroup trialSeminormedAddCommGroup
  trialNormedSpace trialInnerProductSpace trialDualTopology

theorem heatH1Trajectory_integrated_norm_sq_le (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (h : H10 Ω hΩ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖heatH1Trajectory S h t‖ ^ 2) ≤ T * ‖h‖ ^ 2 := by
  have hc := (heatH1Trajectory_continuous S h).norm.pow 2
  have hi := intervalIntegral.integral_mono_on (μ := volume) hT (hc.intervalIntegrable 0 T)
    (continuous_const.intervalIntegrable 0 T) (fun t ht =>
      pow_le_pow_left₀ (norm_nonneg _) (heatH1Trajectory_norm_le S h ht.1) 2)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, Pi.pow_apply] using hi

theorem heatH1Trajectory_memLp (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (h : H10 Ω hΩ) (T : ℝ) : MemLp (heatH1Trajectory S h) 2 (volume.restrict (Icc (0 : ℝ) T)) := by
  have hc := heatH1Trajectory_continuous S h
  exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    ((hc.norm.pow 2).integrableOn_Icc)

theorem heatH1Velocity_memLp (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (h : H10 Ω hΩ) (T : ℝ) : MemLp (heatH1Velocity S h) 2 (volume.restrict (Icc (0 : ℝ) T)) := by
  have hc := heatH1Velocity_continuous S h
  exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    ((hc.norm.pow 2).integrableOn_Icc)

noncomputable def heatH1InEnergySpace (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (h : H10 Ω hΩ) (T : ℝ) : HeatEnergySpace Ω hΩ T :=
  (heatH1Trajectory_memLp S h T).toLp (heatH1Trajectory S h)

/-- The Bochner space of physical L² time derivatives. -/
noncomputable abbrev HeatVelocitySpace (Ω : Set (Space n)) (T : ℝ) :=
  Lp (DomainL2 Ω) 2 (volume.restrict (Icc (0 : ℝ) T))

instance heatVelocitySecondCountable (Ω : Set (Space n)) (T : ℝ) :
    SecondCountableTopology (HeatVelocitySpace Ω T) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  exact inferInstanceAs (SecondCountableTopology
    (Lp (DomainL2 Ω) 2 (volume.restrict (Icc (0 : ℝ) T))))

noncomputable def heatH1VelocityInL2 (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (h : H10 Ω hΩ) (T : ℝ) : HeatVelocitySpace Ω T :=
  (heatH1Velocity_memLp S h T).toLp (heatH1Velocity S h)

theorem heatH1InEnergySpace_ae (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (h : H10 Ω hΩ) (T : ℝ) :
    heatH1InEnergySpace S h T =ᵐ[volume.restrict (Icc (0 : ℝ) T)] heatH1Trajectory S h :=
  MemLp.coeFn_toLp _

theorem heatH1VelocityInL2_ae (S : Submodule ℝ (H10 Ω hΩ)) [FiniteDimensional ℝ S]
    (h : H10 Ω hΩ) (T : ℝ) :
    heatH1VelocityInL2 S h T =ᵐ[volume.restrict (Icc (0 : ℝ) T)] heatH1Velocity S h :=
  MemLp.coeFn_toLp _

theorem heatH1InEnergySpace_norm_sq_le (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (h : H10 Ω hΩ) {T : ℝ} (hT : 0 ≤ T) :
    ‖heatH1InEnergySpace S h T‖ ^ 2 ≤ T * ‖h‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have hi : (∫ t in Icc (0 : ℝ) T,
      inner ℝ (heatH1InEnergySpace S h T t) (heatH1InEnergySpace S h T t)) =
      ∫ t in Icc (0 : ℝ) T, ‖heatH1Trajectory S h t‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [heatH1InEnergySpace_ae S h T] with t ht
    rw [ht, real_inner_self_eq_norm_sq]
  rw [hi, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
  exact heatH1Trajectory_integrated_norm_sq_le S h hT

theorem heatH1VelocityInL2_norm_sq_le (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (h : H10 Ω hΩ) {T : ℝ} (hT : 0 ≤ T) :
    ‖heatH1VelocityInL2 S h T‖ ^ 2 ≤ ‖h‖ ^ 2 / 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have hi : (∫ t in Icc (0 : ℝ) T,
      inner ℝ (heatH1VelocityInL2 S h T t) (heatH1VelocityInL2 S h T t)) =
      ∫ t in Icc (0 : ℝ) T, ‖heatH1Velocity S h t‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [heatH1VelocityInL2_ae S h T] with t ht
    rw [ht, real_inner_self_eq_norm_sq]
  rw [hi, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
  exact heatH1Velocity_integrated_norm_sq_le S h T

/-- One subsequence makes the state and its actual physical time derivative converge weakly. -/
theorem heatH1_exists_joint_weak_subsequence (S : ℕ → Submodule ℝ (H10 Ω hΩ))
    [∀ k, FiniteDimensional ℝ (S k)] (h : H10 Ω hΩ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ u : HeatEnergySpace Ω hΩ T, ∃ d : HeatVelocitySpace Ω T,
      ‖u‖ ≤ Real.sqrt T * ‖h‖ ∧ ‖d‖ ≤ Real.sqrt (1 / 2) * ‖h‖ ∧
      ∃ r : ℕ → ℕ, StrictMono r ∧
        (∀ w : HeatEnergySpace Ω hΩ T,
          Tendsto (fun k => inner ℝ (heatH1InEnergySpace (S (r k)) h T) w)
            atTop (𝓝 (inner ℝ u w))) ∧
        (∀ w : HeatVelocitySpace Ω T,
          Tendsto (fun k => inner ℝ (heatH1VelocityInL2 (S (r k)) h T) w)
            atTop (𝓝 (inner ℝ d w))) := by
  have hu (k : ℕ) : ‖heatH1InEnergySpace (S k) h T‖ ≤ Real.sqrt T * ‖h‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hT]
    exact heatH1InEnergySpace_norm_sq_le (S k) h hT
  obtain ⟨u, hu, r, hr, hur⟩ := PDE.exists_weakly_convergent_subsequence
    (V := HeatEnergySpace Ω hΩ T) (fun k => heatH1InEnergySpace (S k) h T) hu
  have hd (k : ℕ) : ‖heatH1VelocityInL2 (S (r k)) h T‖ ≤ Real.sqrt (1 / 2) * ‖h‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hb := heatH1VelocityInL2_norm_sq_le (S (r k)) h hT
    linarith
  obtain ⟨d, hd, s, hs, hds⟩ := PDE.exists_weakly_convergent_subsequence
    (V := HeatVelocitySpace Ω T) (fun k => heatH1VelocityInL2 (S (r k)) h T) hd
  exact ⟨u, d, hu, hd, r ∘ s, hr.comp hs,
    fun w => (hur w).comp hs.tendsto_atTop, hds⟩
end PDE
