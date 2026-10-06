import PDE.UnitCubeCoordinates
import PDE.WeakCubePoincare

/-! Mean Poincaré on the actual distributional H¹ graph of the open unit cube.
No boundary condition, ACL representative, or Poincaré estimate is assumed. -/

open MeasureTheory Set
open scoped ENNReal

namespace PDE

private theorem first_cube_slices {f df : Space 3 → ℝ}
    (hw : HasWeakPartialOn (unitOpenCube 3) 0 f df)
    (hf : MemLp f 2 (volume.restrict (unitOpenCube 3)))
    (hd : MemLp df 2 (volume.restrict (unitOpenCube 3))) :
    ∀ᵐ y ∂unitSquareMeasure, HasWeakDerivativeOnInterval 0 1
      (fun t => f ![t, y.1, y.2]) (fun t => df ![t, y.1, y.2]) := by
  rw [unitOpenCube_succ] at hw hf hd
  have hs := hw.ae_interval_slices (isOpen_unitOpenCube 2) hf hd
  exact squareCoordinates_measurePreserving.quasiMeasurePreserving.tendsto_ae.eventually hs

private theorem second_cube_slices {f df : Space 3 → ℝ}
    (hw : HasWeakPartialOn (unitOpenCube 3) 1 f df)
    (hf : MemLp f 2 (volume.restrict (unitOpenCube 3)))
    (hd : MemLp df 2 (volume.restrict (unitOpenCube 3))) :
    ∀ᵐ x ∂unitIntervalMeasure, ∀ᵐ z ∂unitIntervalMeasure,
      HasWeakDerivativeOnInterval 0 1 (fun t => f ![x, t, z]) (fun t => df ![x, t, z]) := by
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  have hw' := hw.permuteCoordinates (isOpen_unitOpenCube 3).measurableSet hf hd e
  have hμ := permuteCoordinates_measurePreserving e (isOpen_unitOpenCube 3).measurableSet
  rw [unitOpenCube_permute] at hw' hμ
  have he : e 1 = 0 := by simp [e]
  rw [he] at hw'
  have hs := first_cube_slices hw' (hf.comp_measurePreserving hμ) (hd.comp_measurePreserving hμ)
  have hp (t x z : ℝ) : permuteCoordinates e ![t, x, z] = ![x, t, z] := by
    ext i
    fin_cases i <;> simp [e, Equiv.swap_apply_def]
  simp only [hp] at hs
  exact Measure.ae_ae_of_ae_prod hs

private theorem third_cube_slices {f df : Space 3 → ℝ}
    (hw : HasWeakPartialOn (unitOpenCube 3) 2 f df)
    (hf : MemLp f 2 (volume.restrict (unitOpenCube 3)))
    (hd : MemLp df 2 (volume.restrict (unitOpenCube 3))) :
    ∀ᵐ x ∂unitIntervalMeasure, ∀ᵐ y ∂unitIntervalMeasure,
      HasWeakDerivativeOnInterval 0 1 (fun t => f ![x, y, t]) (fun t => df ![x, y, t]) := by
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 2
  have hw' := hw.permuteCoordinates (isOpen_unitOpenCube 3).measurableSet hf hd e
  have hμ := permuteCoordinates_measurePreserving e (isOpen_unitOpenCube 3).measurableSet
  rw [unitOpenCube_permute] at hw' hμ
  have he : e 2 = 0 := by simp [e]
  rw [he] at hw'
  have hs := first_cube_slices hw' (hf.comp_measurePreserving hμ) (hd.comp_measurePreserving hμ)
  have hp (t x y : ℝ) : permuteCoordinates e ![t, x, y] = ![y, x, t] := by
    ext i
    fin_cases i <;> simp [e, Equiv.swap_apply_def]
  simp only [hp] at hs
  have hs' :=
    (Measure.measurePreserving_swap (μ := unitIntervalMeasure) (ν := unitIntervalMeasure)).quasiMeasurePreserving.tendsto_ae.eventually hs
  exact Measure.ae_ae_of_ae_prod hs'

/-- Geometric mean Poincaré for a function and its actual three distributional
weak derivatives on the open unit cube. No trace restriction is imposed. -/
theorem unitOpenCube_mean_poincare {f : Space 3 → ℝ} {df : Fin 3 → Space 3 → ℝ}
    (hf : MemLp f 2 (volume.restrict (unitOpenCube 3)))
    (hd : ∀ i, MemLp (df i) 2 (volume.restrict (unitOpenCube 3)))
    (hw : ∀ i, HasWeakPartialOn (unitOpenCube 3) i f (df i)) :
    (∫ x in unitOpenCube 3, (f x - ∫ y in unitOpenCube 3, f y) ^ 2) ≤
      ∫ x in unitOpenCube 3, (df 0 x) ^ 2 + (df 1 x) ^ 2 + (df 2 x) ^ 2 := by
  have hμ := cubeCoordinates_measurePreserving
  have hx := first_cube_slices (hw 0) hf (hd 0)
  have hy := second_cube_slices (hw 1) hf (hd 1)
  have hz := third_cube_slices (hw 2) hf (hd 2)
  have h := unitCube_mean_poincare_of_weak_slices (hf.comp_measurePreserving hμ)
    ((hd 0).comp_measurePreserving hμ) ((hd 1).comp_measurePreserving hμ)
    ((hd 2).comp_measurePreserving hμ) hx hy hz
  simp only [Function.comp_apply] at h
  rw [integral_cubeCoordinates] at h
  have hl := integral_cubeCoordinates (fun x => (f x - ∫ y in unitOpenCube 3, f y) ^ 2)
  have hr := integral_cubeCoordinates (fun x => df 0 x ^ 2 + df 1 x ^ 2 + df 2 x ^ 2)
  rwa [hl, hr] at h

/-- The complete distributional H¹ graph satisfies mean Poincaré with
geometric constant one on the open unit cube, including nonzero boundary data. -/
theorem H1.unitOpenCube_mean_poincare (u : H1 (unitOpenCube 3)) :
    (∫ x in unitOpenCube 3,
      (H1.value (unitOpenCube 3) u x - ∫ y in unitOpenCube 3, H1.value (unitOpenCube 3) u y) ^ 2) ≤
      ∫ x in unitOpenCube 3, ∑ i : Fin 3, H1.derivative (unitOpenCube 3) i u x ^ 2 := by
  have h := PDE.unitOpenCube_mean_poincare (Lp.memLp (H1.value (unitOpenCube 3) u))
    (fun i => Lp.memLp (H1.derivative (unitOpenCube 3) i u)) u.hasWeakPartialOn
  simpa only [Fin.sum_univ_three] using h

/-- The actual H¹ derivative energy controls the ordinary unweighted L²
oscillation, in the norm used by the temperature mass-anchoring estimates. -/
theorem H1.unitOpenCube_mean_poincare_lpNorm (u : H1 (unitOpenCube 3)) :
    lpNorm (fun x => H1.value (unitOpenCube 3) u x -
      ∫ y in unitOpenCube 3, H1.value (unitOpenCube 3) u y) 2
        (volume.restrict (unitOpenCube 3)) ≤
      Real.sqrt (∫ x in unitOpenCube 3, ∑ i : Fin 3, H1.derivative (unitOpenCube 3) i u x ^ 2) := by
  have hf : MemLp (fun x => H1.value (unitOpenCube 3) u x -
      ∫ y in unitOpenCube 3, H1.value (unitOpenCube 3) u y) 2
        (volume.restrict (unitOpenCube 3)) := (Lp.memLp _).sub (memLp_const _)
  rw [lpNorm_two_eq_sqrt_integral_sq hf]
  exact Real.sqrt_le_sqrt u.unitOpenCube_mean_poincare

/-- The uniform geometric estimate in precisely the H¹ norm convention used
by positive-mass temperature estimates. Its constant is proved to be one. -/
theorem H1.unitOpenCube_mean_poincare_gradient (u : H1 (unitOpenCube 3)) :
    lpNorm (fun x => H1.value (unitOpenCube 3) u x -
      (∫ y in unitOpenCube 3, H1.value (unitOpenCube 3) u y) /
        (volume.restrict (unitOpenCube 3)).real univ) 2
        (volume.restrict (unitOpenCube 3)) ≤
      Real.sqrt (∑ i : Fin 3, ‖H1.derivative (unitOpenCube 3) i u‖ ^ 2) := by
  simpa only [probReal_univ, div_one, H1.integral_gradient_sq] using
    u.unitOpenCube_mean_poincare_lpNorm

end PDE
