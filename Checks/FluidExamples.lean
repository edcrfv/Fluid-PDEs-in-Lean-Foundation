import PDE.MaterialDerivative
import PDE.NewtonianStress
import PDE.IncompressibleEnergy
import Mathlib.Analysis.Calculus.Deriv.Pi

/-! Concrete checks of the time-dependent material derivative and a mixed stress term. -/

open PDE

-- Both explicit time dependence and movement contribute to this derivative.
example (t : ℝ) :
    materialDerivative (fun _ _ _ => 1) (fun s (x : Space 1) => s * x 0)
      t (fun _ => t) = 2 * t := by
  have hf : DifferentiableAt ℝ
      (Function.uncurry (fun s (x : Space 1) => s * x 0)) (t, fun _ => t) := by
    unfold Function.uncurry
    fun_prop
  have hX : HasDerivAt (fun s : ℝ => (fun _ : Fin 1 => s)) (fun _ => 1) t := by
    exact hasDerivAt_pi.mpr (fun _ => hasDerivAt_id t)
  have h := deriv_material_along_characteristic (u := fun _ _ _ => 1) hf hX
  rw [← h]
  simpa [pow_two] using! ((hasDerivAt_id t).pow 2).deriv

private def crossField (x : Space 2) : Space 2 := fun i => if i = 0 then x 0 * x 1 else 0

private theorem crossField_smooth (i : Fin 2) : ContDiff ℝ 2 (fun x => crossField x i) := by
  fin_cases i <;> simp [crossField] <;> fun_prop

private theorem coord_apply (i j : Fin 2) (x : Space 2) :
    coordDeriv i (fun y : Space 2 => y j) x = if j = i then 1 else 0 := by
  simp [coordDeriv, (hasFDerivAt_apply j x).fderiv, Pi.single_apply, eq_comm]

private theorem cross_partial (i : Fin 2) (x : Space 2) :
    coordDeriv i (fun y : Space 2 => y 0 * y 1) x =
      if i = 0 then x 1 else x 0 := by
  rw [coordDeriv_mul (differentiableAt_apply 0 x) (differentiableAt_apply 1 x)]
  fin_cases i <;> simp [coord_apply]

-- Δu = 0 and grad(div u) = (0,1): this checks the mixed term and tensor-index convention.
example (μ lam : ℝ) (x : Space 2) :
    tensorDivergence (newtonianStress μ lam crossField) x 1 = lam + μ := by
  have hz (j : Fin 2) : coordDeriv j (fun _ : Space 2 => (0 : ℝ)) = fun _ => 0 := by
    funext y
    simp [coordDeriv]
  have hdiv : divergence crossField = fun y => y 1 := by
    funext y
    simp [divergence, crossField, Fin.sum_univ_two, cross_partial, hz]
  rw [tensorDivergence_newtonianStress crossField_smooth, hdiv]
  simp [laplacian, crossField, hz, coord_apply]
