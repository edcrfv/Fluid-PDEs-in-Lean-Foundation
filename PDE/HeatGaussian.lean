import PDE.VectorCalculus
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The normalized heat kernel in arbitrary spatial dimension

`heatGaussian t x = (sqrt (4πt))⁻ⁿ exp (-Σᵢ xᵢ² / (4t))`.
For positive time it is jointly smooth, positive, integrable with mass one,
and solves the heat equation using the library's coordinate Laplacian.
The exponent uses the physical sum of squares, not the ambient supremum norm.

Normalization reuses Mathlib's one-dimensional Gaussian integral and finite
product Fubini theorem. The pinned reference's one-dimensional heat-kernel
module was consulted in the source inventory; this module proves the arbitrary-
dimensional formula directly from Mathlib calculus and integration results.

This is a positive-time kernel ingredient. No initial Dirac limit, causal
extension, local representation formula, or weak-solution regularity follows
from this file alone.
-/

open MeasureTheory
open scoped ContDiff BigOperators

namespace PDE

noncomputable def heatGaussianFactor (t : ℝ) : ℝ :=
  (Real.sqrt (4 * Real.pi * t))⁻¹

noncomputable def heatGaussian {n : ℕ} (t : ℝ) (x : Space n) : ℝ :=
  heatGaussianFactor t ^ n * Real.exp (-(∑ i, x i ^ 2) / (4 * t))

theorem heatGaussian_pos {n : ℕ} {t : ℝ} (ht : 0 < t) (x : Space n) :
    0 < heatGaussian t x := by
  unfold heatGaussian heatGaussianFactor
  positivity

private theorem heatGaussian_eq_prod {n : ℕ} (t : ℝ) (x : Space n) :
    heatGaussian t x = ∏ i, heatGaussianFactor t * Real.exp (-(x i ^ 2) / (4 * t)) := by
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum, heatGaussian]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

private theorem integrable_gaussian_one {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => heatGaussianFactor t * Real.exp (-(x ^ 2) / (4 * t))) := by
  have h := (integrable_exp_neg_mul_sq (b := (4 * t)⁻¹) (by positivity)).const_mul
    (heatGaussianFactor t)
  convert h using 1
  ext x
  congr 2
  ring_nf

private theorem integral_gaussian_one {t : ℝ} (ht : 0 < t) :
    (∫ x : ℝ, heatGaussianFactor t * Real.exp (-(x ^ 2) / (4 * t))) = 1 := by
  have heq : (fun x : ℝ => Real.exp (-(x ^ 2) / (4 * t))) =
      (fun x => Real.exp (-(4 * t)⁻¹ * x ^ 2)) := by ext x; congr 1; ring_nf
  rw [integral_const_mul, heq, integral_gaussian]
  simp only [heatGaussianFactor, div_inv_eq_mul]
  have : Real.pi * (4 * t) = 4 * Real.pi * t := by ring_nf
  rw [this, inv_mul_cancel₀ (by positivity)]

theorem heatGaussian_integrable {n : ℕ} {t : ℝ} (ht : 0 < t) :
    Integrable (heatGaussian (n := n) t) := by
  change Integrable (fun x : Fin n → ℝ => heatGaussian t x) (Measure.pi fun _ => volume)
  simp_rw [heatGaussian_eq_prod]
  exact Integrable.fintype_prod (fun _ : Fin n => integrable_gaussian_one ht)

theorem heatGaussian_integral {n : ℕ} {t : ℝ} (ht : 0 < t) :
    (∫ x : Space n, heatGaussian t x) = 1 := by
  simp_rw [heatGaussian_eq_prod]
  rw [integral_fintype_prod_volume_eq_prod (fun _ : Fin n =>
    fun x : ℝ => heatGaussianFactor t * Real.exp (-(x ^ 2) / (4 * t)))]
  simp [integral_gaussian_one ht]

theorem heatGaussian_contDiffAt {n : ℕ} {p : ℝ × Space n} (ht : 0 < p.1) :
    ContDiffAt ℝ ∞ (fun q : ℝ × Space n => heatGaussian q.1 q.2) p := by
  unfold heatGaussian heatGaussianFactor
  have hn : (4 : ℝ) * Real.pi * p.1 ≠ 0 := by positivity
  have hs : Real.sqrt (4 * Real.pi * p.1) ≠ 0 := by positivity
  apply ContDiffAt.mul
  · exact (((contDiffAt_const.mul contDiffAt_fst).sqrt hn).inv hs).pow _
  · apply ContDiffAt.exp
    apply ContDiffAt.div
    · exact (ContDiffAt.sum (fun i _ =>
        ((contDiffAt_apply ℝ ℝ (i : Fin n) p.2).comp p contDiffAt_snd).pow 2)).neg
    · exact contDiffAt_const.mul contDiffAt_fst
    · positivity

private theorem hasDerivAt_heatGaussianFactor {t : ℝ} (ht : 0 < t) :
    HasDerivAt heatGaussianFactor (-(1 / (2 * t)) * heatGaussianFactor t) t := by
  have hp : 0 < 4 * Real.pi * t := by positivity
  have hs : Real.sqrt (4 * Real.pi * t) ≠ 0 := by positivity
  have h := (((hasDerivAt_id t).const_mul (4 * Real.pi)).sqrt hp.ne').inv hs
  have heq : -(1 / (2 * t)) * heatGaussianFactor t =
      -(4 * Real.pi * 1 / (2 * Real.sqrt (4 * Real.pi * t))) /
        Real.sqrt (4 * Real.pi * t) ^ 2 := by
    dsimp [heatGaussianFactor]
    field_simp
    rw [Real.sq_sqrt (by positivity : 0 ≤ t * 4 * Real.pi)]
  rw [heq]
  exact h

/-- Time differentiation of the normalized Gaussian in arbitrary dimension. -/
theorem hasDerivAt_heatGaussian_time {n : ℕ} {t : ℝ} (ht : 0 < t) (x : Space n) :
    HasDerivAt (fun s => heatGaussian s x)
      (((∑ i, x i ^ 2) / (4 * t ^ 2) - (n : ℝ) / (2 * t)) * heatGaussian t x) t := by
  have hc : HasDerivAt (fun s => heatGaussianFactor s ^ n)
      (-((n : ℝ) / (2 * t)) * heatGaussianFactor t ^ n) t := by
    apply ((hasDerivAt_heatGaussianFactor ht).pow n).congr_deriv
    cases n with
    | zero => simp
    | succ n => simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]; ring_nf
  have he : HasDerivAt (fun s => -(∑ i, x i ^ 2) / (4 * s))
      ((∑ i, x i ^ 2) / (4 * t ^ 2)) t := by
    have hf : (fun s : ℝ => -(∑ i, x i ^ 2) / (4 * s)) =
        (fun s => (-(∑ i, x i ^ 2) / 4) * s⁻¹) := by ext s; ring_nf
    rw [hf]
    exact ((hasDerivAt_inv ht.ne').const_mul (-(∑ i, x i ^ 2) / 4)).congr_deriv
      (by ring_nf)
  exact (hc.mul he.exp).congr_deriv (by dsimp [heatGaussian]; ring_nf)

/-- Every spatial first derivative of the Gaussian. -/
theorem coordDeriv_heatGaussian {n : ℕ} (t : ℝ) (x : Space n) (i : Fin n) :
    coordDeriv i (heatGaussian t) x = -(x i / (2 * t)) * heatGaussian t x := by
  have hq := HasFDerivAt.sum (u := Finset.univ)
    (fun j _ => (hasFDerivAt_apply (𝕜 := ℝ) (j : Fin n) x).pow 2)
  have he := ((hq.neg.mul_const (4 * t)⁻¹).exp).const_mul (heatGaussianFactor t ^ n)
  simp only [Pi.neg_apply, Finset.sum_apply] at he
  change fderiv ℝ (fun y : Space n =>
    heatGaussianFactor t ^ n * Real.exp (-(∑ j, y j ^ 2) / (4 * t))) x _ = _
  simp only [div_eq_mul_inv]
  rw [he.fderiv]
  simp [heatGaussian, Pi.single_apply, mul_ite]
  ring_nf

theorem heatGaussian_contDiff_space {n : ℕ} (t : ℝ) :
    ContDiff ℝ ∞ (heatGaussian (n := n) t) := by
  unfold heatGaussian
  exact contDiff_const.mul
    (((ContDiff.sum (fun i _ => (contDiff_apply ℝ ℝ (i : Fin n)).pow 2)).neg.div_const
      (4 * t)).exp)

theorem coordDeriv_twice_heatGaussian {n : ℕ} (t : ℝ) (x : Space n) (i : Fin n) :
    coordDeriv i (coordDeriv i (heatGaussian t)) x =
      (x i ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * heatGaussian t x := by
  have hf : coordDeriv i (heatGaussian t) =
      (fun y : Space n => -(y i / (2 * t)) * heatGaussian t y) := by
    ext y
    exact coordDeriv_heatGaussian t y i
  rw [hf]
  have hd := ((hasFDerivAt_apply (𝕜 := ℝ) i x).mul_const (2 * t)⁻¹).neg
  change HasFDerivAt (fun y : Space n => -(y i * (2 * t)⁻¹)) _ x at hd
  have hlin : DifferentiableAt ℝ (fun y : Space n => -(y i / (2 * t))) x :=
    hd.differentiableAt
  rw [coordDeriv_mul hlin ((heatGaussian_contDiff_space t).differentiable (by simp)).differentiableAt,
    coordDeriv_heatGaussian]
  have hcoord : coordDeriv i (fun y : Space n => -(y i / (2 * t))) x = -(1 / (2 * t)) := by
    change fderiv ℝ (fun y : Space n => -(y i * (2 * t)⁻¹)) x _ = _
    rw [hd.fderiv]
    simp
  rw [hcoord]
  ring_nf

/-- The normalized Gaussian solves the homogeneous heat equation for positive time. -/
theorem heatGaussian_solves_heat {n : ℕ} {t : ℝ} (ht : 0 < t) (x : Space n) :
    deriv (fun s => heatGaussian s x) t = laplacian (heatGaussian t) x := by
  rw [(hasDerivAt_heatGaussian_time ht x).deriv]
  simp only [laplacian, coordDeriv_twice_heatGaussian, ← Finset.sum_mul,
    Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring_nf

end PDE
