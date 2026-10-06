import PDE.IntervalWeakChainRule
import Mathlib.Analysis.SpecificLimits.Basic

/-! Bounded smooth scalar approximations of the identity with derivative
bounded by one. They preserve estimates without an assumed higher Lp norm. -/

open Filter
open scoped Topology

namespace PDE

noncomputable def boundedSmoothApprox (n : ℕ) (x : ℝ) : ℝ :=
  x / (1 + x ^ 2 / (n + 1))

private theorem denominator_pos (n : ℕ) (x : ℝ) : 0 < 1 + x ^ 2 / (n + 1) := by
  positivity

theorem boundedSmoothApprox_contDiff (n : ℕ) : ContDiff ℝ 1 (boundedSmoothApprox n) :=
  contDiff_id.div (contDiff_const.add ((contDiff_id.pow 2).div_const ((n : ℝ) + 1)))
    (fun x => (denominator_pos n x).ne')

theorem boundedSmoothApprox_deriv (n : ℕ) (x : ℝ) :
    deriv (boundedSmoothApprox n) x =
      (1 - x ^ 2 / (n + 1)) / (1 + x ^ 2 / (n + 1)) ^ 2 := by
  have h := (hasDerivAt_id x).div
    ((hasDerivAt_const x 1).add (((hasDerivAt_id x).pow 2).div_const (n + 1)))
    (denominator_pos n x).ne'
  rw [show deriv (boundedSmoothApprox n) x = _ from h.deriv]
  simp only [Pi.add_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, mul_one, one_mul, zero_add]
  ring

theorem boundedSmoothApprox_norm_le (n : ℕ) (x : ℝ) :
    ‖boundedSmoothApprox n x‖ ≤ ‖x‖ := by
  simp only [boundedSmoothApprox, Real.norm_eq_abs, abs_div,
    abs_of_pos (denominator_pos n x)]
  apply div_le_self (abs_nonneg _)
  have h : 0 ≤ x ^ 2 / ((n : ℝ) + 1) := by positivity
  linarith

theorem boundedSmoothApprox_norm_bound (n : ℕ) (x : ℝ) :
    ‖boundedSmoothApprox n x‖ ≤ n + 1 := by
  rw [boundedSmoothApprox, Real.norm_eq_abs, abs_div, abs_of_pos (denominator_pos n x),
    div_le_iff₀ (denominator_pos n x)]
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have he : ((n : ℝ) + 1) * (1 + x ^ 2 / (n + 1)) = (n + 1) + x ^ 2 := by
    field_simp
  rw [he]
  nlinarith [sq_nonneg (|x| - 1), sq_abs x, abs_nonneg x, Nat.cast_nonneg (α := ℝ) n]

theorem boundedSmoothApprox_deriv_norm_le (n : ℕ) (x : ℝ) :
    ‖deriv (boundedSmoothApprox n) x‖ ≤ 1 := by
  rw [boundedSmoothApprox_deriv, Real.norm_eq_abs, abs_div,
    abs_of_pos (sq_pos_of_pos (denominator_pos n x)),
    div_le_one (sq_pos_of_pos (denominator_pos n x))]
  have hq : 0 ≤ x ^ 2 / ((n : ℝ) + 1) := by positivity
  have hab : |1 - x ^ 2 / ((n : ℝ) + 1)| ≤ 1 + x ^ 2 / ((n : ℝ) + 1) := by
    apply abs_le.mpr
    constructor <;> linarith
  nlinarith [sq_nonneg (x ^ 2 / ((n : ℝ) + 1))]

theorem boundedSmoothApprox_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => boundedSmoothApprox n x) atTop (𝓝 x) := by
  have h : Tendsto (fun n : ℕ => x ^ 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (x ^ 2)).comp (tendsto_add_atTop_nat 1)
  simpa only [boundedSmoothApprox, Pi.div_def, add_zero, div_one] using
    tendsto_const_nhds.div (tendsto_const_nhds.add h) (by norm_num : (1 : ℝ) + 0 ≠ 0)

end PDE
