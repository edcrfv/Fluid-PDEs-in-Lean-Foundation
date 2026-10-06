import PDE.TimePrimitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Time integration by parts

Adapters to Mathlib’s vector-valued integration-by-parts theorem, retaining the
initial datum in the closed-interval formulation used by weak evolution equations.
-/

open MeasureTheory Set
namespace PDE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Classical vector-valued time integration by parts, retaining both endpoint terms. -/
theorem time_integrated_of_hasDerivAt (u du : ℝ → E)
    (hu : ∀ t, HasDerivAt u (du t) t) (hdu : Continuous du)
    (η η' : ℝ → ℝ) (hη : ∀ t, HasDerivAt η (η' t) t) (hη' : Continuous η') (a b : ℝ) :
    (∫ t in a..b, η' t • u t) + (∫ t in a..b, η t • du t) =
      η b • u b - η a • u a := by
  have huc : Continuous u := continuous_iff_continuousAt.mpr fun t => (hu t).continuousAt
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun t => (hη t).continuousAt
  have he := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    hηc.continuousOn huc.continuousOn (fun t _ => hη t) (fun t _ => hu t)
    (hη'.intervalIntegrable (μ := volume) a b) (hdu.intervalIntegrable (μ := volume) a b)
  rw [he]
  abel

/-- The initial-value form over a closed interval whose final test value vanishes. -/
theorem time_integrated_initial_of_hasDerivAt (u du : ℝ → E)
    (hu : ∀ t, HasDerivAt u (du t) t) (hdu : Continuous du)
    (η η' : ℝ → ℝ) (hη : ∀ t, HasDerivAt η (η' t) t) (hη' : Continuous η')
    {a b : ℝ} (hab : a ≤ b) (hηb : η b = 0) :
    (∫ t in Icc a b, η' t • u t) + (∫ t in Icc a b, η t • du t) = (-η a) • u a := by
  have he := time_integrated_of_hasDerivAt u du hu hdu η η' hη hη' a b
  simpa only [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    hηb, zero_smul, zero_sub, neg_smul] using he
end PDE
