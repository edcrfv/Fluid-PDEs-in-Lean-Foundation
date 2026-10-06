import PDE.WeakCubeSobolevSix
import PDE.BoundedSmoothApproximation
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Bounded approximation removes the higher-integrability premise from
the cube Sobolev inequality. All norms come from actual weak line derivatives. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE

/-- The cube L⁶ inequality from weak line differentiation, with no L⁶
membership premise. Bounded smooth approximations and Fatou prove the estimate. -/
theorem unitOpenCube_eLpNorm_six_le_of_weak_slices
    {f : Space 3 → ℝ} {df : Fin 3 → Space 3 → ℝ}
    (hf : Measurable f) (hd : ∀ i, Measurable (df i))
    (hw : ∀ i : Fin 3, ∀ᵐ x ∂volume.restrict (unitOpenCube 3),
      HasWeakDerivativeOnInterval 0 1 (fun t => f (Function.update x i t))
        (fun t => df i (Function.update x i t))) :
    eLpNorm f 6 (volume.restrict (unitOpenCube 3)) ≤
      eLpNorm f 2 (volume.restrict (unitOpenCube 3)) +
        4 * ∑ i : Fin 3, eLpNorm (df i) 2 (volume.restrict (unitOpenCube 3)) := by
  let μ := volume.restrict (unitOpenCube 3)
  let F := fun n x => boundedSmoothApprox n (f x)
  let D := fun n i x => deriv (boundedSmoothApprox n) (f x) * df i x
  have hFm (n : ℕ) : Measurable (F n) := (boundedSmoothApprox_contDiff n).continuous.measurable.comp hf
  have hDm (n : ℕ) (i : Fin 3) : Measurable (D n i) :=
    (((boundedSmoothApprox_contDiff n).continuous_deriv (by simp)).measurable.comp hf).mul (hd i)
  have hF6 (n : ℕ) : MemLp (F n) 6 μ :=
    MemLp.of_bound (hFm n).aestronglyMeasurable (n + 1)
      (Eventually.of_forall fun x => boundedSmoothApprox_norm_bound n (f x))
  have hW (n : ℕ) (i : Fin 3) : ∀ᵐ x ∂μ,
      HasWeakDerivativeOnInterval 0 1 (fun t => F n (Function.update x i t))
        (fun t => D n i (Function.update x i t)) := by
    filter_upwards [hw i] with x hx
    exact hx.comp_contDiff (by norm_num) (boundedSmoothApprox_contDiff n)
  have hF (n : ℕ) : eLpNorm (F n) 2 μ ≤ eLpNorm f 2 μ :=
    eLpNorm_mono fun x => boundedSmoothApprox_norm_le n (f x)
  have hD (n : ℕ) (i : Fin 3) : eLpNorm (D n i) 2 μ ≤ eLpNorm (df i) 2 μ := by
    apply eLpNorm_mono
    intro x
    change ‖deriv (boundedSmoothApprox n) (f x) * df i x‖ ≤ ‖df i x‖
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (boundedSmoothApprox_deriv_norm_le n (f x))
      (norm_nonneg _)).trans_eq (one_mul _)
  have hbound (n : ℕ) : eLpNorm (F n) 6 μ ≤
      eLpNorm f 2 μ + 4 * ∑ i : Fin 3, eLpNorm (df i) 2 μ :=
    (unitOpenCube_eLpNorm_six_le_of_memLp_of_weak_slices (hFm n) (hDm n) (hF6 n) (hW n)).trans
      (add_le_add (hF n) (mul_le_mul le_rfl (Finset.sum_le_sum fun i _ => hD n i) (by positivity) (by positivity)))
  exact Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hbound)
    (fun n => (hFm n).aestronglyMeasurable)
    (Eventually.of_forall fun x => boundedSmoothApprox_tendsto (f x))

end PDE
