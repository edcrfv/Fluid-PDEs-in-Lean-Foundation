import PDE.CoordinatePermutation
import PDE.CubePoincare

/-! Open unit cubes in the actual spatial representation, with explicit
Lebesgue measure identifications and coordinate maps for the square and cube. -/

open MeasureTheory Set

namespace PDE

def unitOpenCube (n : ℕ) : Set (Space n) := {x | ∀ i, x i ∈ Ioo 0 1}

theorem isOpen_unitOpenCube (n : ℕ) : IsOpen (unitOpenCube n) := by
  have h := isOpen_iInter_of_finite fun i : Fin n =>
    (isOpen_Ioo : IsOpen (Ioo (0 : ℝ) 1)).preimage
      (continuous_apply i : Continuous (fun x : Space n => x i))
  have he : unitOpenCube n = ⋂ i : Fin n, (fun x : Space n => x i) ⁻¹' Ioo 0 1 := by
    ext x
    simp [unitOpenCube]
  rwa [he]

theorem unitOpenCube_measure_eq (n : ℕ) :
    volume.restrict (unitOpenCube n) = Measure.pi (fun _ : Fin n => unitIntervalMeasure) := by
  have hs : unitOpenCube n = univ.pi (fun _ : Fin n => Ioo (0 : ℝ) 1) := by
    ext x
    simp [unitOpenCube]
  rw [hs]
  change (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict
    (univ.pi (fun _ => Ioo 0 1)) = _
  rw [Measure.restrict_congr_set Measure.pi_Ioo_ae_eq_pi_Icc]
  exact Measure.restrict_pi_pi (fun _ : Fin n => (volume : Measure ℝ)) (fun _ => Icc 0 1)

instance unitOpenCube_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (volume.restrict (unitOpenCube n)) := by
  rw [unitOpenCube_measure_eq]
  infer_instance

theorem unitOpenCube_succ (n : ℕ) :
    unitOpenCube (n + 1) = intervalCylinder 0 1 (unitOpenCube n) := by
  ext x
  simp only [unitOpenCube, intervalCylinder, mem_ofPred_eq]
  exact Fin.forall_fin_succ

theorem unitOpenCube_permute {n : ℕ} (e : Equiv.Perm (Fin n)) :
    permuteCoordinates e ⁻¹' unitOpenCube n = unitOpenCube n := by
  ext x
  simp only [mem_preimage, unitOpenCube, mem_ofPred_eq, permuteCoordinates_apply]
  exact ⟨fun h i => by simpa using h (e.symm i), fun h i => h (e i)⟩

/-- The pair-to-vector map for the transverse square. -/
def squareCoordinates : (ℝ × ℝ) ≃L[ℝ] Space 2 :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm

@[simp] theorem squareCoordinates_apply (z : ℝ × ℝ) : squareCoordinates z = ![z.1, z.2] := rfl

theorem squareCoordinates_measurePreserving :
    MeasurePreserving squareCoordinates unitSquareMeasure (volume.restrict (unitOpenCube 2)) := by
  rw [unitOpenCube_measure_eq]
  exact MeasurePreserving.symm (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ)
    (measurePreserving_piFinTwo (fun _ : Fin 2 => unitIntervalMeasure))

/-- The nested-product coordinates used by the geometric cube estimates. -/
def cubeCoordinates : (ℝ × (ℝ × ℝ)) ≃L[ℝ] Space 3 :=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr squareCoordinates).trans
    (Fin.consEquivL ℝ (fun _ : Fin 3 => ℝ))

@[simp] theorem cubeCoordinates_apply (z : ℝ × (ℝ × ℝ)) :
    cubeCoordinates z = ![z.1, z.2.1, z.2.2] := rfl

theorem cubeCoordinates_measurePreserving :
    MeasurePreserving cubeCoordinates unitCubeMeasure (volume.restrict (unitOpenCube 3)) := by
  rw [unitOpenCube_succ]
  exact (cylinderLift_measurePreserving 0 1 (isOpen_unitOpenCube 2).measurableSet).comp
    ((MeasurePreserving.id unitIntervalMeasure).prod squareCoordinates_measurePreserving)

theorem integral_cubeCoordinates (f : Space 3 → ℝ) :
    (∫ z, f (cubeCoordinates z) ∂unitCubeMeasure) = ∫ x in unitOpenCube 3, f x :=
  cubeCoordinates_measurePreserving.integral_comp cubeCoordinates.toHomeomorph.measurableEmbedding f

end PDE
