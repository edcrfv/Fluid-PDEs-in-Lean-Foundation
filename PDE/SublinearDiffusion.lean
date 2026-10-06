import PDE.WeightedGradientYoung
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! A density diffusion defect can vanish without a uniform bound on the
first-power diffusion energy. The exponent must be strictly below one half. -/

open Filter
open scoped Topology

namespace PDE

theorem tendsto_zero_of_sublinear_bound {X a b : ℕ → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hX : ∀ j, 0 ≤ X j) (hb : ∀ j, 0 ≤ b j)
    (hbound : ∀ j, X j ≤ a j + b j * (X j) ^ r)
    (ha0 : Tendsto a atTop (𝓝 0)) (hb0 : Tendsto b atTop (𝓝 0)) :
    Tendsto X atTop (𝓝 0) := by
  have ha := ha0.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have hb' := hb0.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have hsmall : ∀ᶠ j in atTop, X j ≤ a j + b j := by
    filter_upwards [ha, hb'] with j haj hbj
    have hx1 : X j ≤ 1 := by
      by_contra hn
      have hx := lt_of_not_ge hn
      have hp := Real.rpow_le_self_of_one_le hx.le hr1
      have hm := mul_le_mul_of_nonneg_left hp (hb j)
      have hh := hbound j
      nlinarith
    exact (hbound j).trans (by
      have hp := Real.rpow_le_one (hX j) hx1 hr
      nlinarith [mul_le_mul_of_nonneg_left hp (hb j)])
  exact squeeze_zero' (Eventually.of_forall hX) hsmall (by simpa using ha0.add hb0)

/-- Subcritical growth of the absolute compression work is sufficient. In
particular, `ν * E` is not required to be uniformly bounded. -/
theorem tendsto_quadratic_energy_of_sublinear_work {ν E : ℕ → ℝ} {A K r : ℝ}
    (hr : 0 ≤ r) (hrhalf : r < 1 / 2) (hK : 0 ≤ K)
    (hν : ∀ j, 0 ≤ ν j) (hE : ∀ j, 0 ≤ E j)
    (hbound : ∀ j, ν j * E j ≤ A + K * (1 + E j) ^ r)
    (hν0 : Tendsto ν atTop (𝓝 0)) :
    Tendsto (fun j => ν j ^ 2 * E j) atTop (𝓝 0) := by
  let X := fun j => ν j ^ 2 * (1 + E j)
  have hpower (j : ℕ) :
      ν j * (1 + E j) ^ r = (ν j) ^ (1 - 2 * r) * (X j) ^ r := by
    by_cases hz : ν j = 0
    · simp [X, hz, Real.zero_rpow (by linarith : 1 - 2 * r ≠ 0)]
    · have hv : 0 < ν j := lt_of_le_of_ne (hν j) (Ne.symm hz)
      dsimp [X]
      rw [Real.mul_rpow (sq_nonneg _) (by linarith [hE j]),
        ← Real.rpow_natCast (ν j) 2, ← Real.rpow_mul (hν j),
        ← mul_assoc, ← Real.rpow_add hv]
      ring_nf
      rw [Real.rpow_one]
      exact mul_comm _ _
  have hx : Tendsto X atTop (𝓝 0) := by
    apply tendsto_zero_of_sublinear_bound hr (by linarith)
      (fun j => mul_nonneg (sq_nonneg _) (by linarith [hE j]))
      (fun j => mul_nonneg hK (Real.rpow_nonneg (hν j) _))
      (a := fun j => A * ν j + ν j ^ 2)
      (b := fun j => K * (ν j) ^ (1 - 2 * r))
    · intro j
      have hb := mul_le_mul_of_nonneg_left (hbound j) (hν j)
      have hp := hpower j
      change ν j ^ 2 * (1 + E j) ≤ _
      nlinarith [congrArg (fun z : ℝ => K * z) hp]
    · simpa using (hν0.const_mul A).add (hν0.pow 2)
    · simpa using (hν0.rpow_const_nhds_zero (by linarith : 0 < 1 - 2 * r)).const_mul K
  apply squeeze_zero (fun j => mul_nonneg (sq_nonneg _) (hE j)) (g := X)
  · intro j
    dsimp [X]
    nlinarith [sq_nonneg (ν j)]
  · exact hx

end PDE
