import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! A differential restriction on nonlinear tests. The inequality
`f'' * f ≥ 2 * (f')²` makes the reciprocal concave wherever f is positive.
Such a positive test cannot reach zero at a finite right endpoint. -/

open Set Filter
open scoped Topology

namespace PDE

theorem concaveOn_inv_of_differential_inequality
    {S : Set ℝ} {f f' f'' : ℝ → ℝ} (hS : Convex ℝ S)
    (hf : ∀ x ∈ S, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ S, HasDerivAt f' (f'' x) x)
    (hpos : ∀ x ∈ S, 0 < f x)
    (hineq : ∀ x ∈ S, 2 * f' x ^ 2 ≤ f'' x * f x) :
    ConcaveOn ℝ S (fun x => (f x)⁻¹) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos hS
    (f' := fun x => -f' x / f x ^ 2)
    (f'' := fun x => (2 * f' x ^ 2 - f'' x * f x) / f x ^ 3)
  · intro x hx
    exact ((hf x hx).inv (hpos x hx).ne').continuousAt.continuousWithinAt
  · intro x hx
    exact ((hf x (interior_subset hx)).inv (hpos x (interior_subset hx)).ne').hasDerivWithinAt
  · intro x hx
    have hh := interior_subset hx
    have h := ((hf' x hh).neg.div ((hf x hh).pow 2) (pow_ne_zero 2 (hpos x hh).ne'))
    apply HasDerivAt.hasDerivWithinAt
    convert! h using 1
    simp only [Pi.pow_apply, Pi.neg_apply]
    field_simp [(hpos x hh).ne']
    ring
  · intro x hx
    exact div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (hineq x (interior_subset hx))) (pow_nonneg (hpos x (interior_subset hx)).le _)

/-- A positive function with concave reciprocal cannot vanish continuously at
a finite endpoint. Only one derivative, at the left endpoint, is needed here. -/
theorem not_concaveOn_inv_of_zero_endpoint
    {a b d : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hpos : ∀ x ∈ Ico a b, 0 < f x)
    (ha : HasDerivAt f d a) (hb : ContinuousAt f b) (hzero : f b = 0) :
    ¬ ConcaveOn ℝ (Ico a b) (fun x => (f x)⁻¹) := by
  intro hconc
  have hfa := hpos a ⟨le_rfl, hab⟩
  let v := -d / f a ^ 2
  have hbound : ∀ᶠ x in 𝓝[<] b, 1 ≤ ((x - a) * v + (f a)⁻¹) * f x := by
    filter_upwards [Ioo_mem_nhdsLT hab] with x hx
    have hs := hconc.slope_le_of_hasDerivAt ⟨le_rfl, hab⟩ ⟨hx.1.le, hx.2⟩ hx.1
      (ha.inv hfa.ne')
    rw [slope_def_field] at hs
    have hlinear : (f x)⁻¹ ≤ (x - a) * v + (f a)⁻¹ := by
      have := (div_le_iff₀ (sub_pos.mpr hx.1)).mp hs
      dsimp [v]
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hlinear (hpos x ⟨hx.1.le, hx.2⟩).le
    simpa only [inv_mul_cancel₀ (hpos x ⟨hx.1.le, hx.2⟩).ne'] using hh
  have hlim : Tendsto (fun x => ((x - a) * v + (f a)⁻¹) * f x)
      (𝓝[<] b) (𝓝 0) := by
    have hc : ContinuousAt (fun x => ((x - a) * v + (f a)⁻¹) * f x) b :=
      (((continuousAt_id.sub continuousAt_const).mul continuousAt_const).add continuousAt_const).mul hb
    simpa only [hzero, mul_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have : (1 : ℝ) ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim hbound
  norm_num at this

theorem not_differential_inequality_of_zero_endpoint
    {a b : ℝ} {f f' f'' : ℝ → ℝ} (hab : a < b)
    (hf : ∀ x ∈ Ico a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ico a b, HasDerivAt f' (f'' x) x)
    (hpos : ∀ x ∈ Ico a b, 0 < f x)
    (hb : ContinuousAt f b) (hzero : f b = 0) :
    ¬ (∀ x ∈ Ico a b, 2 * f' x ^ 2 ≤ f'' x * f x) := by
  intro hineq
  exact not_concaveOn_inv_of_zero_endpoint hab hpos (hf a ⟨le_rfl, hab⟩) hb hzero
    (concaveOn_inv_of_differential_inequality (convex_Ico a b) hf hf' hpos hineq)

end PDE
