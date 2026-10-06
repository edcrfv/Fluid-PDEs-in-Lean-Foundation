import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Quadratic energy budgets pass under weak convergence in a real Hilbert
space. The proof uses a fixed supporting affine functional at the limit, so it
does not require strong convergence or convergence of the energies. -/

open Filter InnerProductSpace
open scoped Topology

namespace PDE

/-- Lower semicontinuity in the form needed for an energy inequality with
convergent endpoint and source terms. Even testing against the limit suffices. -/
theorem energy_budget_of_weak_limit
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {u : ℕ → V} {v : V} {F S : ℕ → ℝ} {f s κ : ℝ}
    (hκ : 0 ≤ κ)
    (hu : Tendsto (fun j => inner ℝ (u j) v) atTop (𝓝 (inner ℝ v v)))
    (hF : Tendsto F atTop (𝓝 f)) (hS : Tendsto S atTop (𝓝 s))
    (hb : ∀ j, F j + κ * ‖u j‖ ^ 2 ≤ S j) :
    f + κ * ‖v‖ ^ 2 ≤ s := by
  have hsupport (j : ℕ) : 2 * inner ℝ (u j) v - ‖v‖ ^ 2 ≤ ‖u j‖ ^ 2 := by
    have h := sq_nonneg ‖u j - v‖
    rw [norm_sub_sq_real] at h
    linarith
  have hlim := hF.add ((hu.const_mul 2 |>.sub_const (‖v‖ ^ 2)).const_mul κ)
  have hle := le_of_tendsto_of_tendsto hlim hS
    (Filter.Eventually.of_forall fun j =>
      (add_le_add (le_refl (F j)) (mul_le_mul_of_nonneg_left (hsupport j) hκ)).trans (hb j))
  simpa only [real_inner_self_eq_norm_sq, two_mul, add_sub_cancel_right] using hle

/-- The same lower semicontinuity for the physical sum of squared component
norms, rather than the supremum norm of an unbundled product. -/
theorem energy_budget_of_weak_limit_finite
    {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {u : ℕ → ι → V} {v : ι → V} {F S : ℕ → ℝ} {f s κ : ℝ}
    (hκ : 0 ≤ κ)
    (hu : ∀ i, Tendsto (fun j => inner ℝ (u j i) (v i)) atTop
      (𝓝 (inner ℝ (v i) (v i))))
    (hF : Tendsto F atTop (𝓝 f)) (hS : Tendsto S atTop (𝓝 s))
    (hb : ∀ j, F j + κ * ∑ i, ‖u j i‖ ^ 2 ≤ S j) :
    f + κ * ∑ i, ‖v i‖ ^ 2 ≤ s := by
  let U (j : ℕ) : PiLp 2 (fun _ : ι => V) := WithLp.toLp 2 (u j)
  let W : PiLp 2 (fun _ : ι => V) := WithLp.toLp 2 v
  have hweak : Tendsto (fun j => inner ℝ (U j) W) atTop (𝓝 (inner ℝ W W)) := by
    simpa only [PiLp.inner_apply, U, W, WithLp.toLp_ofLp] using
      tendsto_finsetSum Finset.univ (fun i _ => hu i)
  have h := energy_budget_of_weak_limit hκ hweak hF hS
    (by simpa only [PiLp.norm_sq_eq_of_L2, U, WithLp.toLp_ofLp] using hb)
  simpa only [PiLp.norm_sq_eq_of_L2, W, WithLp.toLp_ofLp] using h

end PDE
