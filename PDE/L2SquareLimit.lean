import Mathlib.MeasureTheory.Function.L2Space

/-! Strong L² convergence gives strong L¹ convergence of squares, without a
common pointwise majorant. This supplies density-square pressure convergence. -/

open Filter MeasureTheory InnerProductSpace
open scoped Topology

namespace PDE

private theorem integral_norm_mul_norm_le_L2
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (f g : Lp ℝ 2 μ) :
    (∫ x, ‖f x‖ * ‖g x‖ ∂μ) ≤ ‖f‖ * ‖g‖ := by
  let F := (Lp.memLp f).norm.toLp (fun x => ‖f x‖)
  let G := (Lp.memLp g).norm.toLp (fun x => ‖g x‖)
  have hFn : ‖F‖ = ‖f‖ := by
    change ‖(Lp.memLp f).norm.toLp (fun x => ‖f x‖)‖ = ‖f‖
    rw [Lp.norm_toLp, eLpNorm_norm, Lp.norm_def]
  have hGn : ‖G‖ = ‖g‖ := by
    change ‖(Lp.memLp g).norm.toLp (fun x => ‖g x‖)‖ = ‖g‖
    rw [Lp.norm_toLp, eLpNorm_norm, Lp.norm_def]
  have he : (∫ x, ‖f x‖ * ‖g x‖ ∂μ) = inner ℝ F G := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(Lp.memLp f).norm.coeFn_toLp, (Lp.memLp g).norm.coeFn_toLp] with x hx hy
    simp only [Real.inner_apply, F, G, hx, hy]
  rw [he, ← hFn, ← hGn]
  exact real_inner_le_norm _ _

/-- The L¹ square-difference estimate expressed in actual L² class norms. -/
theorem integral_norm_sq_sub_sq_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (f g : Lp ℝ 2 μ) :
    (∫ x, ‖f x ^ 2 - g x ^ 2‖ ∂μ) ≤ ‖f - g‖ * ‖f + g‖ := by
  have he : (∫ x, ‖f x ^ 2 - g x ^ 2‖ ∂μ) =
      ∫ x, ‖(f - g) x‖ * ‖(f + g) x‖ ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub f g, Lp.coeFn_add f g] with x hs ha
    rw [hs, ha, ← norm_mul]
    congr 1
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [he]
  exact integral_norm_mul_norm_le_L2 _ _

/-- Density squares converge strongly in L¹ whenever their actual L² classes
converge strongly. No a.e. convergence of density is needed for this implication. -/
theorem tendsto_integral_norm_sq_sub_sq_of_L2
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ} (h : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun j => ∫ x, ‖f j x ^ 2 - g x ^ 2‖ ∂μ) atTop (𝓝 0) := by
  apply squeeze_zero (fun j => integral_nonneg fun x => norm_nonneg _)
    (fun j => integral_norm_sq_sub_sq_le (f j) g)
  simpa using (tendsto_iff_norm_sub_tendsto_zero.mp h).mul (h.add_const g).norm

end PDE
