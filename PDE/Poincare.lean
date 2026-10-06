import PDE.SobolevZero
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Tactic.Finiteness

/-!
# Poincaré on bounded open domains in dimension at least three

We use Mathlib's smooth compact-support Sobolev inequality at exponent 2 < n,
compare the Fréchet derivative with its coordinate derivatives, and extend by H¹ density.
The constant depends only on the bounded domain and dimension. No boundary regularity
is required for H₀¹, which is defined by closure. Dimensions one and two need another argument.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PDE

/-- Coordinate control of the operator norm for the sup norm on `Space n`. -/
theorem norm_clm_le_sum_coordinates {n : ℕ} (A : Space n →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ i : Fin n, ‖A (Pi.single i 1)‖ := by
  apply A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro x
  have hx : x = ∑ i : Fin n, x i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  calc
    ‖A x‖ = ‖∑ i : Fin n, x i • A (Pi.single i 1)‖ := by
      conv_lhs => rw [hx]
      rw [map_sum]
      simp only [map_smul]
    _ ≤ ∑ i : Fin n, ‖x i • A (Pi.single i 1)‖ := norm_sum_le _ _
    _ = ∑ i : Fin n, ‖A (Pi.single i 1)‖ * ‖x i‖ := by
      simp only [norm_smul, mul_comm]
    _ ≤ ∑ i : Fin n, ‖A (Pi.single i 1)‖ * ‖x‖ :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (norm_le_pi_norm x i)
        (norm_nonneg _)
    _ = (∑ i : Fin n, ‖A (Pi.single i 1)‖) * ‖x‖ := (Finset.sum_mul _ _ _).symm

/-- A sum of scalar L² derivative norms bounds the L² norm of the full derivative. -/
theorem eLpNorm_fderiv_le_sum_coordDeriv {n : ℕ} {Ω : Set (Space n)}
    {φ : Space n → ℝ} (hφ : IsTestFunctionOn Ω φ) :
    eLpNorm (fderiv ℝ φ) 2 volume ≤ ∑ i : Fin n, eLpNorm (coordDeriv i φ) 2 volume := by
  calc
    eLpNorm (fderiv ℝ φ) 2 volume ≤
        eLpNorm (∑ i : Fin n, fun x => ‖coordDeriv i φ x‖) 2 volume := by
      apply eLpNorm_mono
      intro x
      rw [Finset.sum_apply, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
      exact norm_clm_le_sum_coordinates (fderiv ℝ φ x)
    _ ≤ ∑ i : Fin n, eLpNorm (fun x => ‖coordDeriv i φ x‖) 2 volume :=
      eLpNorm_sum_le (fun i _ => (hφ.coordDeriv_continuous i).norm.aestronglyMeasurable)
        (by norm_num)
    _ = _ := by simp only [eLpNorm_norm]

noncomputable def poincareConstant {n : ℕ} (Ω : Set (Space n)) : ℝ≥0 :=
  eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure (Space n)) Ω 2 2

/-- The smooth case, with all constants independent of the test function. -/
theorem poincare_testFunction {n : ℕ} (hn : 2 < n) {Ω : Set (Space n)}
    (hb : Bornology.IsBounded Ω) {φ : Space n → ℝ} (hφ : IsTestFunctionOn Ω φ) :
    ‖H1.value Ω (H1.ofTestFunction φ hφ)‖ ≤
      poincareConstant Ω * ∑ i : Fin n, ‖H1.derivative Ω i (H1.ofTestFunction φ hφ)‖ := by
  have hd (i : Fin n) : eLpNorm (coordDeriv i φ) 2 volume ≠ ∞ :=
    ((hφ.coordDeriv_continuous i).memLp_of_hasCompactSupport
      (hφ.coordDeriv_hasCompactSupport i)).2.ne
  have h := eLpNorm_le_eLpNorm_fderiv (volume : Measure (Space n))
    (hφ.contDiff.of_le (by simp)) ((subset_tsupport φ).trans hφ.tsupport_subset)
    (p := 2) (by norm_num) (by simpa [Space] using hn) hb
  change eLpNorm φ 2 volume ≤ (poincareConstant Ω : ℝ≥0∞) *
    eLpNorm (fderiv ℝ φ) 2 volume at h
  have he : eLpNorm φ 2 volume ≤ (poincareConstant Ω : ℝ≥0∞) *
      ∑ i : Fin n, eLpNorm (coordDeriv i φ) 2 volume :=
    h.trans (by gcongr; exact eLpNorm_fderiv_le_sum_coordDeriv hφ)
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.sum_ne_top.mpr fun i _ => hd i)) he
  simpa only [H1.norm_value_ofTestFunction, H1.norm_derivative_ofTestFunction,
    ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_sum (fun i _ => hd i)] using hreal

/-- Poincaré extended to the complete zero-boundary Sobolev space by density. -/
theorem H10.poincare {n : ℕ} (hn : 2 < n) {Ω : Set (Space n)} {hΩ : IsOpen Ω}
    (hb : Bornology.IsBounded Ω) (u : H10 Ω hΩ) :
    ‖H1.value Ω u.val‖ ≤ poincareConstant Ω * ∑ i : Fin n, ‖H1.derivative Ω i u.val‖ := by
  apply H10.induction_of_isClosed (s := {v | ‖H1.value Ω v‖ ≤
    poincareConstant Ω * ∑ i : Fin n, ‖H1.derivative Ω i v‖}) ?_ ?_ u
  · exact isClosed_le (H1.value Ω).continuous.norm
      (continuous_const.mul (continuous_finsetSum _ fun i _ => (H1.derivative Ω i).continuous.norm))
  · intro φ hφ
    exact poincare_testFunction hn hb hφ

end PDE
