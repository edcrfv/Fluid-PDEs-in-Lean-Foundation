import PDE.MassForm
import PDE.LinearEvolution

/-!
# Finite-dimensional evolution with a physical mass pairing

The operator M⁻¹K is constructed from an injective physical-space embedding and the stiffness
form. Its exponential gives a global solution. The weak equation, physical-norm energy identity
and contraction for nonnegative stiffness are proved with constants independent of dimension.
-/

open InnerProductSpace MeasureTheory
namespace PDE
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- M⁻¹K, with the mass operator obtained from the physical Hilbert embedding. -/
noncomputable def massEvolutionOperator (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) : V →L[ℝ] V :=
  (massForm_isCoercive J hJ).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (continuousLinearMapOfBilin B)

theorem massEvolutionOperator_spec (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (u v : V) :
    massForm J (massEvolutionOperator J hJ B u) v = B u v := by
  rw [← (massForm_isCoercive J hJ).continuousLinearEquivOfBilin_apply]
  change inner ℝ ((massForm_isCoercive J hJ).continuousLinearEquivOfBilin
    ((massForm_isCoercive J hJ).continuousLinearEquivOfBilin.symm
      (continuousLinearMapOfBilin B u))) v = B u v
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact continuousLinearMapOfBilin_apply B u v

/-- A global solution of the finite-dimensional equation M u′ + K u = 0. -/
noncomputable def massEvolution (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (u₀ : V) : ℝ → V :=
  linearEvolution (massEvolutionOperator J hJ B) u₀

theorem massEvolution_zero (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (u₀ : V) : massEvolution J hJ B u₀ 0 = u₀ :=
  linearEvolution_zero _ _

theorem massEvolution_hasDerivAt (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (u₀ : V) (t : ℝ) :
    HasDerivAt (massEvolution J hJ B u₀)
      (-massEvolutionOperator J hJ B (massEvolution J hJ B u₀ t)) t :=
  linearEvolution_hasDerivAt _ _ _

/-- The weak-in-space finite-dimensional ODE, tested against every trial vector. -/
theorem massEvolution_weakEquation (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (u₀ v : V) (t : ℝ) :
    HasDerivAt (fun s => inner ℝ (J (massEvolution J hJ B u₀ s)) (J v))
      (-(B (massEvolution J hJ B u₀ t) v)) t := by
  have hd := (J.hasFDerivAt.comp_hasDerivAt t
    (massEvolution_hasDerivAt J hJ B u₀ t)).inner ℝ (hasDerivAt_const t (J v))
  have hp : inner ℝ (J (massEvolutionOperator J hJ B (massEvolution J hJ B u₀ t))) (J v) =
      B (massEvolution J hJ B u₀ t) v := massEvolutionOperator_spec J hJ B _ _
  simpa only [Function.comp_def, map_neg, inner_zero_right, inner_neg_left, zero_add, hp] using hd

/-- Differential energy in the physical Hilbert norm, rather than the trial-space norm. -/
theorem massEvolution_energy_hasDerivAt (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (u₀ : V) (t : ℝ) :
    HasDerivAt (fun s => ‖J (massEvolution J hJ B u₀ s)‖ ^ 2)
      (-2 * B (massEvolution J hJ B u₀ t) (massEvolution J hJ B u₀ t)) t := by
  have hd := (J.hasFDerivAt.comp_hasDerivAt t
    (massEvolution_hasDerivAt J hJ B u₀ t)).norm_sq
  have hp : inner ℝ (J (massEvolution J hJ B u₀ t))
      (J (massEvolutionOperator J hJ B (massEvolution J hJ B u₀ t))) =
        B (massEvolution J hJ B u₀ t) (massEvolution J hJ B u₀ t) := by
    rw [real_inner_comm]
    exact massEvolutionOperator_spec J hJ B _ _
  simpa only [Function.comp_def, map_neg, inner_neg_right, hp, mul_neg, neg_mul] using hd

/-- Exact integrated energy identity for the constructed mass-matrix evolution. -/
theorem massEvolution_energy_identity (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (u₀ : V) (T : ℝ) :
    ‖J (massEvolution J hJ B u₀ T)‖ ^ 2 +
      2 * (∫ t in (0 : ℝ)..T, B (massEvolution J hJ B u₀ t) (massEvolution J hJ B u₀ t)) =
        ‖J u₀‖ ^ 2 := by
  have hu : Continuous (massEvolution J hJ B u₀) := continuous_iff_continuousAt.mpr
    fun t => (massEvolution_hasDerivAt J hJ B u₀ t).continuousAt
  have hd : Continuous (fun t => -2 * B (massEvolution J hJ B u₀ t) (massEvolution J hJ B u₀ t)) :=
    continuous_const.mul ((B.continuous.comp hu).clm_apply hu)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => massEvolution_energy_hasDerivAt J hJ B u₀ t) (hd.intervalIntegrable 0 T)
  rw [intervalIntegral.integral_const_mul, massEvolution_zero] at hi
  linarith

/-- Nonnegative stiffness gives a bound independent of trial dimension and mass inverse norm. -/
theorem massEvolution_norm_le (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v, 0 ≤ B v v) (u₀ : V)
    {T : ℝ} (hT : 0 ≤ T) : ‖J (massEvolution J hJ B u₀ T)‖ ≤ ‖J u₀‖ := by
  have he := massEvolution_energy_identity J hJ B u₀ T
  have hi : 0 ≤ ∫ t in (0 : ℝ)..T,
      B (massEvolution J hJ B u₀ t) (massEvolution J hJ B u₀ t) :=
    intervalIntegral.integral_nonneg hT (fun t _ => hB _)
  nlinarith [norm_nonneg (J (massEvolution J hJ B u₀ T)), norm_nonneg (J u₀)]
end PDE
