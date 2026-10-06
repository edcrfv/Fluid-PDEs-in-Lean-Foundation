import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

/-!
# Smooth approximation: an existing Mathlib entrypoint

This is uniform approximation of uniformly continuous functions.
Approximation in `W^{k,p}`, preservation of support near a boundary, and weak-derivative
commutation are later milestones and do not follow just from this wrapper.
-/

open scoped ContDiff

namespace PDE

theorem exists_smooth_uniform_approximation
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} (hf : UniformContinuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ x, dist (g x) (f x) < ε :=
  hf.exists_contDiff_dist_le hε

end PDE
