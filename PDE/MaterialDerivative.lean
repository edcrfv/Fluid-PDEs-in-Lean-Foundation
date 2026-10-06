import PDE.VectorCalculus
import PDE.Transport
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Material derivative of a time-dependent scalar field

The chain rule assumes joint differentiability in space and time, and a supplied
differentiable trajectory with velocity `u`. It does not construct a flow.
-/

namespace PDE

variable {n : ℕ}

noncomputable def timeDerivative (f : ℝ → Space n → ℝ) (t : ℝ) (x : Space n) : ℝ :=
  deriv (fun s => f s x) t

noncomputable def materialDerivative (u : ℝ → Space n → Space n)
    (f : ℝ → Space n → ℝ) (t : ℝ) (x : Space n) : ℝ :=
  timeDerivative f t x + advection (u t) (f t) x

/-- Time-dependent chain rule, with the actual Eulerian time and spatial derivatives. -/
theorem hasDerivAt_material_along_characteristic
    {f : ℝ → Space n → ℝ} {u : ℝ → Space n → Space n}
    {X : ℝ → Space n} {t : ℝ}
    (hf : DifferentiableAt ℝ (Function.uncurry f) (t, X t))
    (hX : HasDerivAt X (u t (X t)) t) :
    HasDerivAt (fun s => f s (X s)) (materialDerivative u f t (X t)) t := by
  let L := fderiv ℝ (Function.uncurry f) (t, X t)
  have ht : HasDerivAt (fun s => f s (X t)) (L (1, 0)) t := by
    simpa [L, Function.comp_def, Function.uncurry] using!
      hf.hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t (X t)))
  have hs : HasFDerivAt (f t)
      (L.comp ((0 : Space n →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Space n)))) (X t) :=
    hf.hasFDerivAt.comp (X t)
      ((hasFDerivAt_const t (X t)).prodMk (hasFDerivAt_id (X t)))
  have hsplit : L (1, u t (X t)) = L (1, 0) + L (0, u t (X t)) := by
    rw [← map_add]
    simp
  have hvalue : materialDerivative u f t (X t) = L (1, u t (X t)) := by
    rw [materialDerivative, timeDerivative, ht.deriv, advection_eq_fderiv, hs.fderiv]
    simpa using hsplit.symm
  rw [hvalue]
  simpa [L, Function.comp_def, Function.uncurry] using!
    hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hX)

theorem deriv_material_along_characteristic
    {f : ℝ → Space n → ℝ} {u : ℝ → Space n → Space n}
    {X : ℝ → Space n} {t : ℝ}
    (hf : DifferentiableAt ℝ (Function.uncurry f) (t, X t))
    (hX : HasDerivAt X (u t (X t)) t) :
    deriv (fun s => f s (X s)) t = materialDerivative u f t (X t) :=
  (hasDerivAt_material_along_characteristic hf hX).deriv

end PDE
