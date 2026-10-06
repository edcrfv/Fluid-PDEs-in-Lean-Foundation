import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Differentiation along a characteristic

The chain rule below assumes that a differentiable curve has already been supplied.
It does not construct a characteristic flow or prove a transport well-posedness theorem.
-/

namespace PDE

theorem hasDerivAt_along_characteristic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} {X : ℝ → E} {t : ℝ} {v : E} {L : E →L[ℝ] ℝ}
    (hφ : HasFDerivAt φ L (X t)) (hX : HasDerivAt X v t) :
    HasDerivAt (fun s => φ (X s)) (L v) t :=
  hφ.comp_hasDerivAt t hX

end PDE
