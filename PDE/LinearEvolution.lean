import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.ODE.Gronwall

/-!
# Bounded linear evolution and energy identities

The operator exponential constructs the global solution of u′ = -Au. Its initial value,
ODE and integrated energy identity are proved. Accretivity gives norm contraction.
This is a bounded-operator result, suitable for finite-dimensional Galerkin equations;
an unbounded Dirichlet Laplacian is not an input to this construction.
-/

open InnerProductSpace MeasureTheory Set
namespace PDE
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Global solution operator for the bounded linear ODE u' = -Au. -/
noncomputable def linearEvolution (A : V →L[ℝ] V) (u₀ : V) (t : ℝ) : V :=
  NormedSpace.exp (t • (-A)) u₀

omit [CompleteSpace V] in
theorem linearEvolution_zero (A : V →L[ℝ] V) (u₀ : V) : linearEvolution A u₀ 0 = u₀ := by
  simp [linearEvolution]

theorem linearEvolution_hasDerivAt (A : V →L[ℝ] V) (u₀ : V) (t : ℝ) :
    HasDerivAt (linearEvolution A u₀) (-A (linearEvolution A u₀ t)) t := by
  unfold linearEvolution
  simpa [mul_apply_eq_comp] using
    (hasDerivAt_exp_smul_const' (-A) t).clm_apply (hasDerivAt_const t u₀)

omit [CompleteSpace V] in
/-- The differential energy identity for a supplied differentiable linear ODE solution. -/
theorem linearODE_energy_hasDerivAt (A : V →L[ℝ] V) (u : ℝ → V)
    (hODE : ∀ t, HasDerivAt u (-A (u t)) t) (t : ℝ) :
    HasDerivAt (fun s => ‖u s‖ ^ 2) (-2 * inner ℝ (u t) (A (u t))) t := by
  simpa only [inner_neg_right, mul_neg, neg_mul] using (hODE t).norm_sq

omit [CompleteSpace V] in
/-- The integrated energy identity, with all time integrals justified by continuity. -/
theorem linearODE_energy_identity (A : V →L[ℝ] V) (u : ℝ → V)
    (hODE : ∀ t, HasDerivAt u (-A (u t)) t) (T : ℝ) :
    ‖u T‖ ^ 2 + 2 * (∫ t in (0 : ℝ)..T, inner ℝ (u t) (A (u t))) = ‖u 0‖ ^ 2 := by
  have hu : Continuous u := continuous_iff_continuousAt.mpr fun t => (hODE t).continuousAt
  have hd : Continuous (fun t => -2 * inner ℝ (u t) (A (u t))) :=
    continuous_const.mul (hu.inner (A.continuous.comp hu))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => linearODE_energy_hasDerivAt A u hODE t) (hd.intervalIntegrable 0 T)
  rw [intervalIntegral.integral_const_mul] at h
  linarith

omit [CompleteSpace V] in
/-- Accretivity gives an estimate independent of the norm of the evolution operator. -/
theorem linearODE_norm_le_initial (A : V →L[ℝ] V)
    (hA : ∀ v, 0 ≤ inner ℝ v (A v)) (u : ℝ → V)
    (hODE : ∀ t, HasDerivAt u (-A (u t)) t) {T : ℝ} (hT : 0 ≤ T) :
    ‖u T‖ ≤ ‖u 0‖ := by
  have he := linearODE_energy_identity A u hODE T
  have hi : 0 ≤ ∫ t in (0 : ℝ)..T, inner ℝ (u t) (A (u t)) :=
    intervalIntegral.integral_nonneg hT (fun t _ => hA (u t))
  nlinarith [norm_nonneg (u T), norm_nonneg (u 0)]

theorem linearEvolution_energy_identity (A : V →L[ℝ] V) (u₀ : V) (T : ℝ) :
    ‖linearEvolution A u₀ T‖ ^ 2 +
      2 * (∫ t in (0 : ℝ)..T, inner ℝ (linearEvolution A u₀ t) (A (linearEvolution A u₀ t))) =
        ‖u₀‖ ^ 2 := by
  simpa only [linearEvolution_zero] using
    linearODE_energy_identity A (linearEvolution A u₀) (linearEvolution_hasDerivAt A u₀) T

theorem linearEvolution_norm_le (A : V →L[ℝ] V) (hA : ∀ v, 0 ≤ inner ℝ v (A v))
    (u₀ : V) {T : ℝ} (hT : 0 ≤ T) : ‖linearEvolution A u₀ T‖ ≤ ‖u₀‖ := by
  simpa only [linearEvolution_zero] using linearODE_norm_le_initial A hA (linearEvolution A u₀)
    (linearEvolution_hasDerivAt A u₀) hT
omit [CompleteSpace V] in
/-- Local-in-time uniqueness for a bounded linear ODE, using right derivatives on the interval. -/
theorem linearODE_unique_on (A : V →L[ℝ] V) {u v : ℝ → V} {a b : ℝ}
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hdu : ∀ t ∈ Ico a b, HasDerivWithinAt u (-A (u t)) (Ici t) t)
    (hdv : ∀ t ∈ Ico a b, HasDerivWithinAt v (-A (v t)) (Ici t) t)
    (hinit : u a = v a) : EqOn u v (Icc a b) := by
  have hd : ∀ t ∈ Ico a b,
      HasDerivWithinAt (u - v) (-A ((u - v) t)) (Ici t) t := by
    intro t ht
    simpa only [Pi.sub_apply, map_sub, neg_sub, neg_sub_neg] using (hdu t ht).sub (hdv t ht)
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (hu.sub hv) hd (by simp [hinit])
    (fun t _ => by simpa only [norm_neg] using A.le_opNorm ((u - v) t))
  intro t ht
  exact sub_eq_zero.mp (hz t ht)

end PDE
