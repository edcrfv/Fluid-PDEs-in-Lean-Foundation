import PDE.UnitCubeCoordinates
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

/-! The product-integral step of the nonzero-boundary cube Sobolev argument.
The line majorant is explicit; later weak-derivative estimates supply it. -/

open MeasureTheory Set
open scoped ENNReal

namespace PDE

/-- A common integrable majorant for the three coordinate-line bounds
controls the L³ᐟ² seminorm. This is a direct application of the grid-lines lemma. -/
theorem unitOpenCube_eLpNorm_le_of_line_integrals {f : Space 3 → ℝ}
    {g : Space 3 → ℝ≥0∞} (hg : Measurable g)
    (hline : ∀ᵐ x ∂volume.restrict (unitOpenCube 3), ∀ i : Fin 3,
      ‖f x‖ₑ ≤ ∫⁻ t, g (Function.update x i t) ∂unitIntervalMeasure) :
    eLpNorm f (3 / 2) (volume.restrict (unitOpenCube 3)) ≤
      ∫⁻ x in unitOpenCube 3, g x := by
  have hp : Real.HolderConjugate (Fintype.card (Fin 3)) (3 / 2) := by
    constructor <;> norm_num
  have hb := lintegral_prod_lintegral_pow_le
    (fun _ : Fin 3 => unitIntervalMeasure) hp hg
  rw [← unitOpenCube_measure_eq] at hb
  norm_num only [Fintype.card_fin, Nat.cast_ofNat, sub_self, sub_zero] at hb
  have hpow : (∫⁻ x in unitOpenCube 3, ‖f x‖ₑ ^ (3 / 2 : ℝ)) ≤
      (∫⁻ x in unitOpenCube 3, g x) ^ (3 / 2 : ℝ) := by
    refine le_trans ?_ hb
    apply lintegral_mono_ae
    filter_upwards [hline] with x hx
    calc
      ‖f x‖ₑ ^ (3 / 2 : ℝ) = ∏ _i : Fin 3, ‖f x‖ₑ ^ (1 / 2 : ℝ) := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
      _ ≤ _ := Finset.prod_le_prod' fun i _ => ENNReal.rpow_le_rpow (hx i) (by norm_num)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
  calc
    _ ≤ ((∫⁻ x in unitOpenCube 3, g x) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) :=
      ENNReal.rpow_le_rpow hpow (by norm_num)
    _ = _ := by rw [← ENNReal.rpow_mul]; norm_num

end PDE
