import PDE.MassEvolution

/-!
# Higher energy for a finite mass evolution

For a symmetric stiffness form, testing the constructed ODE by its time derivative gives
an exact stiffness-energy identity and an integrated physical velocity bound. The physical
mass map is retained explicitly; no infinite-dimensional time regularity is assumed.
-/

open InnerProductSpace MeasureTheory
namespace PDE
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The physical time derivative of the constructed mass evolution. -/
noncomputable def massVelocity (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (u₀ : V) (t : ℝ) : H :=
  J (-massEvolutionOperator J hJ B (massEvolution J hJ B u₀ t))

theorem massVelocity_hasDerivAt (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (u₀ : V) (t : ℝ) :
    HasDerivAt (fun t => J (massEvolution J hJ B u₀ t)) (massVelocity J hJ B u₀ t) t :=
  J.hasFDerivAt.comp_hasDerivAt t (massEvolution_hasDerivAt J hJ B u₀ t)

theorem massVelocity_continuous (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (u₀ : V) : Continuous (massVelocity J hJ B u₀) := by
  have hu : Continuous (massEvolution J hJ B u₀) := continuous_iff_continuousAt.mpr
    fun t => (massEvolution_hasDerivAt J hJ B u₀ t).continuousAt
  exact J.continuous.comp (((massEvolutionOperator J hJ B).continuous.comp hu).neg)

/-- Testing the symmetric stiffness equation by the time derivative dissipates stiffness energy. -/
theorem massEvolution_stiffness_hasDerivAt (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ u v, B u v = B v u) (u₀ : V) (t : ℝ) :
    HasDerivAt (fun t => B (massEvolution J hJ B u₀ t) (massEvolution J hJ B u₀ t))
      (-2 * ‖massVelocity J hJ B u₀ t‖ ^ 2) t := by
  let u := massEvolution J hJ B u₀
  let A := massEvolutionOperator J hJ B
  have hd := (B.hasFDerivAt.comp_hasDerivAt t (massEvolution_hasDerivAt J hJ B u₀ t)).clm_apply
    (massEvolution_hasDerivAt J hJ B u₀ t)
  have hs : B (u t) (A (u t)) = ‖J (A (u t))‖ ^ 2 := by
    rw [← massEvolutionOperator_spec J hJ B (u t) (A (u t)), massForm_apply,
      real_inner_self_eq_norm_sq]
  have hsym : B (A (u t)) (u t) = B (u t) (A (u t)) := hB _ _
  change HasDerivAt (fun t => B (u t) (u t)) (B (-A (u t)) (u t) + B (u t) (-A (u t))) t at hd
  have he : B (-A (u t)) (u t) + B (u t) (-A (u t)) = -2 * ‖massVelocity J hJ B u₀ t‖ ^ 2 := by
    simp only [map_neg, neg_apply, hsym, hs, massVelocity, norm_neg]
    change -‖J (A (u t))‖ ^ 2 + -‖J (A (u t))‖ ^ 2 = -2 * ‖J (A (u t))‖ ^ 2
    ring
  exact hd.congr_deriv he

theorem massEvolution_stiffness_energy_identity (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ u v, B u v = B v u) (u₀ : V) (T : ℝ) :
    B (massEvolution J hJ B u₀ T) (massEvolution J hJ B u₀ T) +
      2 * (∫ t in (0 : ℝ)..T, ‖massVelocity J hJ B u₀ t‖ ^ 2) = B u₀ u₀ := by
  have hc : Continuous (fun t => -2 * ‖massVelocity J hJ B u₀ t‖ ^ 2) :=
    continuous_const.mul ((massVelocity_continuous J hJ B u₀).norm.pow 2)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => massEvolution_stiffness_hasDerivAt J hJ B hB u₀ t)
    (hc.intervalIntegrable (μ := volume) 0 T)
  rw [intervalIntegral.integral_const_mul, massEvolution_zero] at hi
  linarith

theorem massEvolution_integrated_velocity_le (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ u v, B u v = B v u) (hn : ∀ v, 0 ≤ B v v)
    (u₀ : V) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, ‖massVelocity J hJ B u₀ t‖ ^ 2) ≤ B u₀ u₀ / 2 := by
  have he := massEvolution_stiffness_energy_identity J hJ B hB u₀ T
  linarith [hn (massEvolution J hJ B u₀ T)]

theorem massEvolution_stiffness_le (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ u v, B u v = B v u)
    (u₀ : V) {T : ℝ} (hT : 0 ≤ T) :
    B (massEvolution J hJ B u₀ T) (massEvolution J hJ B u₀ T) ≤ B u₀ u₀ := by
  have he := massEvolution_stiffness_energy_identity J hJ B hB u₀ T
  have hi : 0 ≤ ∫ t in (0 : ℝ)..T, ‖massVelocity J hJ B u₀ t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hT (fun t _ => sq_nonneg _)
  linarith
end PDE
