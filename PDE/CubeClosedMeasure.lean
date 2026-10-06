import PDE.UnitCubeCoordinates

/-! The closed and open unit cubes carry the same restricted Lebesgue measure.
This identifies integral domains only; it does not identify boundary conditions. -/

open MeasureTheory Set

namespace PDE

theorem unitOpenCube_restrict_eq_closed (n : ℕ) :
    volume.restrict (unitOpenCube n) = volume.restrict (Icc (0 : Space n) 1) := by
  have hs : unitOpenCube n = univ.pi (fun _ : Fin n => Ioo (0 : ℝ) 1) := by
    ext x
    simp [unitOpenCube]
  rw [hs]
  exact Measure.restrict_congr_set Measure.univ_pi_Ioo_ae_eq_Icc

end PDE
