import PDE.ReciprocalConcavity

/-! A quantitative tail obstruction for positive reciprocal-concave tests.
It only needs concavity on a finite interval containing zero. In particular,
such tests cannot converge to a positive value at an interior point and zero
at a larger point, even if every approximating test has a nonzero tail. -/

open Set Filter
open scoped Topology

namespace PDE

theorem ratio_mul_le_of_inv_concave {h : ℝ → ℝ} {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hpos : ∀ z ∈ Icc 0 y, 0 < h z)
    (hc : ConcaveOn ℝ (Icc 0 y) (fun z => (h z)⁻¹)) :
    (x / y) * h x ≤ h y := by
  have hy : 0 < y := hx.trans_le hxy
  have ha : 0 ≤ 1 - x / y := sub_nonneg.mpr ((div_le_one hy).mpr hxy)
  have hb : 0 ≤ x / y := (div_pos hx hy).le
  have he := hc.2 (show (0 : ℝ) ∈ Icc 0 y from ⟨le_rfl, hy.le⟩)
    (show y ∈ Icc 0 y from ⟨hy.le, le_rfl⟩) ha hb (by ring : 1 - x / y + x / y = 1)
  have hex : (1 - x / y) • (0 : ℝ) + (x / y) • y = x := by
    simp only [smul_eq_mul, mul_zero, zero_add, div_mul_cancel₀ _ hy.ne']
  rw [hex] at he
  simp only [smul_eq_mul] at he
  have h0 : 0 ≤ (1 - x / y) * (h 0)⁻¹ :=
    mul_nonneg ha (inv_nonneg.mpr (hpos 0 ⟨le_rfl, hy.le⟩).le)
  have hle : (x / y) * (h y)⁻¹ ≤ (h x)⁻¹ := le_trans (by linarith) he
  have hpx := hpos x ⟨hx.le, hxy⟩
  have hpy := hpos y ⟨hy.le, le_rfl⟩
  rw [← div_eq_mul_inv, div_le_iff₀ hpy] at hle
  rw [inv_mul_eq_div, le_div_iff₀ hpx] at hle
  exact hle

theorem ratio_mul_le_of_differential_inequality {h h' h'' : ℝ → ℝ} {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y)
    (hd : ∀ z ∈ Icc 0 y, HasDerivAt h (h' z) z)
    (hdd : ∀ z ∈ Icc 0 y, HasDerivAt h' (h'' z) z)
    (hpos : ∀ z ∈ Icc 0 y, 0 < h z)
    (hineq : ∀ z ∈ Icc 0 y, 2 * h' z ^ 2 ≤ h'' z * h z) :
    (x / y) * h x ≤ h y :=
  ratio_mul_le_of_inv_concave hx hxy hpos
    (concaveOn_inv_of_differential_inequality (convex_Icc 0 y) hd hdd hpos hineq)

theorem not_tendsto_zero_of_inv_concave {h : ℕ → ℝ → ℝ} {x y a : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (ha : 0 < a)
    (hpos : ∀ n z, z ∈ Icc 0 y → 0 < h n z)
    (hc : ∀ n, ConcaveOn ℝ (Icc 0 y) (fun z => (h n z)⁻¹))
    (hl : Tendsto (fun n => h n x) atTop (𝓝 a)) :
    ¬ Tendsto (fun n => h n y) atTop (𝓝 0) := by
  intro hz
  have hle := le_of_tendsto_of_tendsto (hl.const_mul (x / y)) hz
    (Filter.Eventually.of_forall fun n => ratio_mul_le_of_inv_concave hx hxy (hpos n) (hc n))
  have hp : 0 < (x / y) * a := mul_pos (div_pos hx (hx.trans_le hxy)) ha
  exact (not_le_of_gt hp) hle

end PDE
