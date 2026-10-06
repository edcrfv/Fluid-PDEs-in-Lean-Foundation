import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-! Natural powers in real Lp seminorms, including the extended-valued cases. -/

open MeasureTheory
open scoped ENNReal

namespace PDE

/-- Taking the n-th power multiplies the Lp exponent and raises the seminorm
to the n-th power. No integrability is assumed in this identity. -/
theorem eLpNorm_real_pow {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) (p : ℝ≥0∞) {n : ℕ} (hn : 0 < n) :
    eLpNorm (fun x => f x ^ n) p μ = eLpNorm f (p * n) μ ^ n := by
  calc
    _ = eLpNorm (fun x => ‖f x‖ ^ (n : ℝ)) p μ := by
      apply eLpNorm_congr_norm_ae
      exact Filter.Eventually.of_forall fun x => by simp
    _ = _ := by
      rw [eLpNorm_norm_rpow f (by exact_mod_cast hn)]
      simp

end PDE
