import PDE.VectorCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Weighted Young estimates for the physical coordinate dot product.
No identification with the ambient supremum norm on `Space n` is used. -/

open MeasureTheory Filter
open scoped Topology

namespace PDE

theorem fluidDot_self_nonneg {n : ℕ} (v : Space n) : 0 ≤ fluidDot v v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem weighted_fluidDot_young {n : ℕ} (p q : Space n) (ν θ : ℝ)
    {A κ : ℝ} (hA : 0 ≤ A) (hκ : 0 < κ) :
    ν * θ * A * fluidDot p q ≤ κ / 2 * A * fluidDot q q +
      ν ^ 2 / (2 * κ) * θ ^ 2 * A * fluidDot p p := by
  have hi (i : Fin n) : ν * θ * A * (p i * q i) ≤
      κ / 2 * A * (q i * q i) + ν ^ 2 / (2 * κ) * θ ^ 2 * A * (p i * p i) := by
    convert! mul_le_mul_of_nonneg_left
      (two_mul_le_add_mul_sq (a := q i) (b := ν * θ * p i) hκ)
      (show 0 ≤ A / 2 by positivity) using 1 <;> ring
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, fluidDot] using h

theorem abs_weighted_fluidDot_young {n : ℕ} (p q : Space n) (ν θ : ℝ)
    {A κ : ℝ} (hA : 0 ≤ A) (hκ : 0 < κ) :
    |ν * θ * A * fluidDot p q| ≤ κ / 2 * A * fluidDot q q +
      ν ^ 2 / (2 * κ) * θ ^ 2 * A * fluidDot p p := by
  apply abs_le.mpr
  constructor
  · have h := weighted_fluidDot_young p q (-ν) θ hA hκ
    simp only [neg_sq, neg_mul] at h
    linarith
  · exact weighted_fluidDot_young p q ν θ hA hκ

/-- A coefficient bound and two genuine energy integrals give integrability
and an absolute-integral bound for the mixed defect. -/
theorem integral_abs_weighted_fluidDot_le {α : Type*} [MeasurableSpace α]
    {m : Measure α} {n : ℕ} {p q : α → Space n} {θ A : α → ℝ} {ν B κ : ℝ}
    (hκ : 0 < κ) (hA : ∀ᵐ x ∂m, 0 ≤ A x)
    (hB : ∀ᵐ x ∂m, θ x ^ 2 * A x ≤ B)
    (hm : AEStronglyMeasurable (fun x => ν * θ x * A x * fluidDot (p x) (q x)) m)
    (hh : Integrable (fun x => A x * fluidDot (q x) (q x)) m)
    (hg : Integrable (fun x => fluidDot (p x) (p x)) m) :
    Integrable (fun x => ν * θ x * A x * fluidDot (p x) (q x)) m ∧
      (∫ x, |ν * θ x * A x * fluidDot (p x) (q x)| ∂m) ≤
        κ / 2 * (∫ x, A x * fluidDot (q x) (q x) ∂m) +
          ν ^ 2 * B / (2 * κ) * (∫ x, fluidDot (p x) (p x) ∂m) := by
  have hmajor : ∀ᵐ x ∂m, |ν * θ x * A x * fluidDot (p x) (q x)| ≤
      κ / 2 * (A x * fluidDot (q x) (q x)) +
        (ν ^ 2 * B / (2 * κ)) * fluidDot (p x) (p x) := by
    filter_upwards [hA, hB] with x hx hb
    have he := mul_le_mul_of_nonneg_left hb
      (show 0 ≤ ν ^ 2 / (2 * κ) * fluidDot (p x) (p x) from
        mul_nonneg (by positivity) (fluidDot_self_nonneg _))
    have hy := abs_weighted_fluidDot_young (p x) (q x) ν (θ x) hx hκ
    calc
      _ ≤ κ / 2 * A x * fluidDot (q x) (q x) +
          ν ^ 2 / (2 * κ) * θ x ^ 2 * A x * fluidDot (p x) (p x) := hy
      _ ≤ κ / 2 * A x * fluidDot (q x) (q x) +
          (ν ^ 2 * B / (2 * κ)) * fluidDot (p x) (p x) := by
        refine add_le_add le_rfl ?_
        convert! he using 1 <;> ring
      _ = _ := by ring
  have hi : Integrable (fun x => κ / 2 * (A x * fluidDot (q x) (q x)) +
      (ν ^ 2 * B / (2 * κ)) * fluidDot (p x) (p x)) m :=
    (hh.const_mul (κ / 2)).add (hg.const_mul (ν ^ 2 * B / (2 * κ)))
  have hd : Integrable (fun x => ν * θ x * A x * fluidDot (p x) (q x)) m :=
    hi.mono' hm (by simpa only [Real.norm_eq_abs] using hmajor)
  refine ⟨hd, ?_⟩
  have hb := integral_mono_ae hd.abs hi hmajor
  simpa only [integral_add (hh.const_mul (κ / 2)) (hg.const_mul (ν ^ 2 * B / (2 * κ))),
    integral_const_mul] using hb

/-- If ν∫|∇ρ|² is bounded, the remaining ν² term vanishes. B and κ are fixed. -/
theorem tendsto_quadratic_diffusion_remainder {ν E : ℕ → ℝ} {B K κ : ℝ}
    (hκ : 0 < κ) (hB : 0 ≤ B) (hν : ∀ j, 0 ≤ ν j) (hE : ∀ j, 0 ≤ E j)
    (hbound : ∀ j, ν j * E j ≤ K) (hlim : Tendsto ν atTop (𝓝 0)) :
    Tendsto (fun j => ν j ^ 2 * B / (2 * κ) * E j) atTop (𝓝 0) := by
  apply squeeze_zero (fun j =>
    mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) hB) (by positivity)) (hE j))
    (g := fun j => (B * K / (2 * κ)) * ν j)
  · intro j
    have h := mul_le_mul_of_nonneg_left (hbound j)
      (show 0 ≤ ν j * B / (2 * κ) from div_nonneg (mul_nonneg (hν j) hB) (by positivity))
    convert! h using 1 <;> ring
  · simpa only [mul_zero] using hlim.const_mul (B * K / (2 * κ))

end PDE
