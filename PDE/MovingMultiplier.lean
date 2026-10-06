import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Strong L¹ convergence is stable under a uniformly bounded, a.e. convergent
sequence of scalar multipliers. No common pointwise majorant for the moving
L¹ functions is required. -/

open Filter MeasureTheory
open scoped Topology

namespace PDE

/-- Pass an integral with both factors moving: the weight converges in L¹ and
the multiplier converges a.e. with a uniform bound. -/
theorem tendsto_integral_mul_of_L1_of_bounded_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f a : ℕ → α → ℝ} {g b : α → ℝ} {K : ℝ}
    (hf : ∀ j, Integrable (f j) μ) (hg : Integrable g μ)
    (ha : ∀ j, AEStronglyMeasurable (a j) μ)
    (haK : ∀ j, ∀ᵐ x ∂μ, ‖a j x‖ ≤ K)
    (hL1 : Tendsto (fun j => ∫ x, ‖f j x - g x‖ ∂μ) atTop (𝓝 0))
    (hab : ∀ᵐ x ∂μ, Tendsto (fun j => a j x) atTop (𝓝 (b x))) :
    Tendsto (fun j => ∫ x, f j x * a j x ∂μ) atTop
      (𝓝 (∫ x, g x * b x ∂μ)) := by
  have hprod (j : ℕ) (w : α → ℝ) (hw : Integrable w μ) :
      Integrable (fun x => w x * a j x) μ := by
    apply (hw.norm.mul_const K).mono' (hw.aestronglyMeasurable.mul (ha j))
    filter_upwards [haK j] with x hx
    simpa only [Pi.mul_apply, Pi.sub_apply, norm_mul] using mul_le_mul_of_nonneg_left hx (norm_nonneg (w x))
  have hfixed : Tendsto (fun j => ∫ x, g x * a j x ∂μ) atTop
      (𝓝 (∫ x, g x * b x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖g x‖ * K)
    · intro j
      exact hg.aestronglyMeasurable.mul (ha j)
    · exact hg.norm.mul_const K
    · intro j
      filter_upwards [haK j] with x hx
      simpa only [Pi.mul_apply, Pi.sub_apply, norm_mul] using mul_le_mul_of_nonneg_left hx (norm_nonneg (g x))
    · filter_upwards [hab] with x hx
      exact tendsto_const_nhds.mul hx
  have herr : Tendsto (fun j => ∫ x, (f j x - g x) * a j x ∂μ) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa using hL1.mul_const K)
    intro j
    calc
      _ ≤ ∫ x, ‖f j x - g x‖ * K ∂μ := by
        apply norm_integral_le_of_norm_le (((hf j).sub hg).norm.mul_const K)
        filter_upwards [haK j] with x hx
        simpa only [Pi.mul_apply, Pi.sub_apply, norm_mul] using mul_le_mul_of_nonneg_left hx (norm_nonneg _)
      _ = _ := integral_mul_const _ _
  have heq (j : ℕ) : (∫ x, f j x * a j x ∂μ) =
      (∫ x, (f j x - g x) * a j x ∂μ) + ∫ x, g x * a j x ∂μ := by
    rw [← integral_add (hprod j (fun x => f j x - g x) ((hf j).sub hg)) (hprod j _ hg)]
    congr 1
    funext x
    ring
  simp_rw [heq]
  simpa using herr.add hfixed

end PDE
