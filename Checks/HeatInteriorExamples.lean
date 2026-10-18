import PDE.HeatInteriorRegularity

open MeasureTheory Set
open scoped ContDiff BigOperators
namespace PDE.HeatInteriorExamples

private def caloricPolynomial (z : Space 2) : ℝ := z 1 ^ 2 + 2 * z 0

private theorem polynomial_coord (i : Fin 2) (z : Space 2) :
    coordDeriv i caloricPolynomial z =
      2 * z 1 * (Pi.single i 1 : Space 2) 1 + 2 * (Pi.single i 1 : Space 2) 0 := by
  have hd := ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) z).pow 2).add
    ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) z).const_mul (2 : ℝ))
  change (fderiv ℝ ((fun z : Space 2 => z 1 ^ 2) + (fun z : Space 2 => 2 * z 0)) z) (Pi.single i 1) = _
  rw [hd.fderiv]
  simp

example : IsDistributionalHeatSolution (Set.univ : Set (Space 2)) caloricPolynomial := by
  apply (isDistributionalHeatSolution_iff_of_contDiffOn isOpen_univ
    (show ContDiffOn ℝ ∞ caloricPolynomial Set.univ from by unfold caloricPolynomial; fun_prop)).mpr
  intro z _
  have hfirst : coordDeriv (1 : Fin 2) caloricPolynomial = fun z => 2 * z 1 := by
    funext z
    simp [polynomial_coord]
  simp only [spaceTimeLaplacian, Fin.sum_univ_one, Fin.succ_zero_eq_one, hfirst]
  rw [polynomial_coord]
  have hd := (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) z).const_mul (2 : ℝ)
  unfold coordDeriv
  rw [hd.fderiv]
  simp

/-- An open cusp: no boundary smoothness predicate enters the theorem. -/
private def cusp : Set (Space 2) := {x | 0 < x 0 ∧ x 0 < 1 ∧ |x 1| < (x 0) ^ 2}

private theorem cusp_isOpen : IsOpen cusp := by
  exact (isOpen_lt continuous_const (continuous_apply 0)).inter
    ((isOpen_lt (continuous_apply 0) continuous_const).inter
      (isOpen_lt (continuous_apply 1).abs ((continuous_apply 0).pow 2)))

-- The result applies to an arbitrary weak solution on this domain, without a
-- pointwise regularity assumption or a Lipschitz-boundary hypothesis.
example (u : Space 3 → ℝ) (hu : IsDistributionalHeatSolution (heatCylinder cusp 1) u) :
    ∃ v : Space 3 → ℝ, ContDiffOn ℝ ∞ v (heatCylinder cusp 1) ∧
      u =ᵐ[volume.restrict (heatCylinder cusp 1)] v ∧
      (∀ z ∈ heatCylinder cusp 1, coordDeriv 0 v z = spaceTimeLaplacian v z) := by
  obtain ⟨v, hv, huv, hcal, _⟩ := heat_interior_smooth (by decide : 0 < 2)
    cusp_isOpen (by norm_num : (0 : ℝ) < 1) hu
  exact ⟨v, hv, huv, hcal⟩

end PDE.HeatInteriorExamples
