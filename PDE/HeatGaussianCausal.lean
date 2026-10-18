/-
The flat-exponential proof pattern below is adapted from Mathlib's
Analysis/SpecialFunctions/SmoothTransition.lean, generalized to real powers.
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Original authors: Sébastien Gouëzel, Yury Kudryashov.
Released under Apache 2.0 license; see LICENSES/Apache-2.0.txt.
-/
import PDE.HeatGaussian
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Smoothness of the causal Gaussian away from its source

For any real a, the zero extension of t^a exp(-1/t) is smooth. This includes the
negative half-integer powers needed in odd spatial dimensions. A rescaling by
the positive spatial sum of squares expresses the heat Gaussian through this
flat function near every point with nonzero spatial coordinate.

For n > 0, the existing Gaussian formula vanishes at nonpositive times and is
jointly smooth off (0,0), including across time zero. This is an ingredient of
the local representation formula, which is not proved in this module.
-/

open Filter Set
open scoped Topology ContDiff

namespace PDE

noncomputable def heatFlatPower (a t : ℝ) : ℝ := t ^ a * expNegInvGlue t

private theorem heatFlatPower_tendsto_zero (a : ℝ) :
    Tendsto (heatFlatPower a) (𝓝 0) (𝓝 0) := by
  change Tendsto (fun x : ℝ => x ^ a * expNegInvGlue x) (𝓝 0) (𝓝 0)
  simp only [expNegInvGlue, mul_ite, mul_zero]
  refine tendsto_const_nhds.if ?_
  simp only [not_le]
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-a) 1 zero_lt_one).comp
    tendsto_inv_nhdsGT_zero
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [Function.comp_apply, neg_one_mul, ← Real.rpow_neg_eq_inv_rpow, neg_neg]

private theorem heatFlatPower_slope (a : ℝ) :
    slope (heatFlatPower a) 0 = heatFlatPower (a - 1) := by
  ext x
  by_cases hx : 0 < x
  · simp only [slope_def_field, heatFlatPower, expNegInvGlue.zero, mul_zero,
      sub_zero, Real.rpow_sub_one hx.ne']
    ring
  · simp [slope_def_field, heatFlatPower, expNegInvGlue.zero_of_nonpos (not_lt.mp hx)]

/-- Real powers multiplied by the flat exponential still have a derivative at zero. -/
theorem hasDerivAt_heatFlatPower (a x : ℝ) :
    HasDerivAt (heatFlatPower a)
      (a * heatFlatPower (a - 1) x + heatFlatPower (a - 2) x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hz (b : ℝ) : heatFlatPower b x = 0 := by
      simp [heatFlatPower, expNegInvGlue.zero_of_nonpos hx.le]
    rw [hz, hz, mul_zero, zero_add]
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [gt_mem_nhds hx] with y hy
    simp [heatFlatPower, expNegInvGlue.zero_of_nonpos hy.le]
  · simp only [heatFlatPower, expNegInvGlue.zero, mul_zero, zero_add]
    rw [hasDerivAt_iff_tendsto_slope]
    change Tendsto (slope (heatFlatPower a) 0) _ _
    rw [heatFlatPower_slope]
    exact (heatFlatPower_tendsto_zero (a - 1)).mono_left inf_le_left
  · have h := (Real.hasDerivAt_rpow_const (p := a) (Or.inl hx.ne')).mul
      (hasDerivAt_inv hx.ne').neg.exp
    have hd : HasDerivAt (fun y : ℝ => y ^ a * Real.exp (-y⁻¹))
        (a * heatFlatPower (a - 1) x + heatFlatPower (a - 2) x) x := by
      apply h.congr_deriv
      simp only [heatFlatPower, expNegInvGlue, ite_eq_right hx.not_ge, Pi.neg_apply,
        Real.rpow_sub hx a 2, Real.rpow_two]
      ring
    apply hd.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hx] with y hy
    simp [heatFlatPower, expNegInvGlue, hy.not_ge]

/-- The zero extension of `t^a exp(-1/t)` is smooth for every real exponent. -/
theorem heatFlatPower_contDiff (a : ℝ) : ContDiff ℝ ∞ (heatFlatPower a) := by
  apply contDiff_all_iff_nat.2 (fun m => ?_) ⊤
  induction m generalizing a with
  | zero =>
    apply contDiff_zero.2
    exact (show Differentiable ℝ (heatFlatPower a) from
      fun x => (hasDerivAt_heatFlatPower a x).differentiableAt).continuous
  | succ m ih =>
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = m + 1 from rfl]
    refine contDiff_succ_iff_deriv.2
      ⟨fun x => (hasDerivAt_heatFlatPower a x).differentiableAt, by simp, ?_⟩
    have hd : deriv (heatFlatPower a) = fun x =>
        a * heatFlatPower (a - 1) x + heatFlatPower (a - 2) x := by
      ext x
      exact (hasDerivAt_heatFlatPower a x).deriv
    rw [hd]
    have h1 : ContDiff ℝ (m : ℕ) (heatFlatPower (a - 1)) := ih (a - 1)
    have h2 : ContDiff ℝ (m : ℕ) (heatFlatPower (a - 2)) := ih (a - 2)
    exact (contDiff_const.mul h1).add h2


theorem heatGaussian_eq_zero_of_nonpos {n : ℕ} (hn : 0 < n)
    {t : ℝ} (ht : t ≤ 0) (x : Space n) : heatGaussian t x = 0 := by
  have hs : Real.sqrt (4 * Real.pi * t) = 0 :=
    Real.sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) ht)
  simp [heatGaussian, heatGaussianFactor, hs, zero_pow hn.ne']

private theorem heatGaussianFactor_rpow (n : ℕ) {t : ℝ} (ht : 0 < t) :
    heatGaussianFactor t ^ n = heatGaussianFactor 1 ^ n * t ^ (-((n : ℝ) / 2)) := by
  have hr : (Real.sqrt t)⁻¹ ^ n = t ^ (-((n : ℝ) / 2)) := by
    rw [inv_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le,
      ← Real.rpow_neg ht.le]
    congr 1
    ring
  simp only [heatGaussianFactor, Real.sqrt_mul (by positivity : 0 ≤ 4 * Real.pi),
    mul_inv_rev, mul_pow, mul_one]
  rw [hr]
  ring

private theorem heatGaussian_eq_flat {n : ℕ} (hn : 0 < n) (t : ℝ) (x : Space n)
    (hx : 0 < (∑ i, x i ^ 2) / 4) :
    heatGaussian t x = heatGaussianFactor 1 ^ n *
      ((∑ i, x i ^ 2) / 4) ^ (-((n : ℝ) / 2)) *
      heatFlatPower (-((n : ℝ) / 2)) (t / ((∑ i, x i ^ 2) / 4)) := by
  by_cases ht : 0 < t
  · have hq : 0 < t / ((∑ i, x i ^ 2) / 4) := div_pos ht hx
    have he : -(∑ i, x i ^ 2) / (4 * t) = -(t / ((∑ i, x i ^ 2) / 4))⁻¹ := by
      field_simp
    simp only [heatGaussian, heatGaussianFactor_rpow n ht, heatFlatPower,
      expNegInvGlue, ite_eq_right hq.not_ge, Real.div_rpow ht.le hx.le, he]
    field_simp
  · rw [heatGaussian_eq_zero_of_nonpos hn (not_lt.mp ht)]
    have hq : t / ((∑ i, x i ^ 2) / 4) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (not_lt.mp ht) hx.le
    simp [heatFlatPower, expNegInvGlue.zero_of_nonpos hq]

private theorem heatGaussian_contDiffAt_of_space_ne_zero {n : ℕ} (hn : 0 < n)
    {p : ℝ × Space n} (hx : p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : ℝ × Space n => heatGaussian q.1 q.2) p := by
  let b : ℝ × Space n → ℝ := fun q => (∑ i, q.2 i ^ 2) / 4
  have hb : ContDiff ℝ ∞ b := by
    apply ContDiff.div_const
    exact ContDiff.sum (fun i _ => ((contDiff_apply ℝ ℝ (i : Fin n)).comp contDiff_snd).pow 2)
  have hpos : 0 < b p := by
    apply div_pos _ (by norm_num)
    obtain ⟨i, hi⟩ : ∃ i, p.2 i ≠ 0 := by
      by_contra h
      apply hx
      ext i
      simpa using not_exists.mp h i
    exact Finset.sum_pos' (fun j _ => sq_nonneg (p.2 j))
      ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
  have hs : ContDiffAt ℝ ∞ (fun q : ℝ × Space n =>
      heatGaussianFactor 1 ^ n * b q ^ (-((n : ℝ) / 2)) *
      heatFlatPower (-((n : ℝ) / 2)) (q.1 / b q)) p :=
    (contDiffAt_const.mul (hb.contDiffAt.rpow_const_of_ne hpos.ne')).mul
      ((heatFlatPower_contDiff _).contDiffAt.comp p
        (contDiffAt_fst.div hb.contDiffAt hpos.ne'))
  apply hs.congr_of_eventuallyEq
  filter_upwards [hb.continuous.continuousAt.eventually (lt_mem_nhds hpos)] with q hq
  exact heatGaussian_eq_flat hn q.1 q.2 hq

/-- The causal Gaussian is jointly smooth away from its space–time source,
including points at time zero with nonzero spatial coordinate. -/
theorem heatGaussian_contDiffAt_off_origin {n : ℕ} (hn : 0 < n)
    {p : ℝ × Space n} (hp : p ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : ℝ × Space n => heatGaussian q.1 q.2) p := by
  rcases lt_trichotomy p.1 0 with ht | ht | ht
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt.eventually (gt_mem_nhds ht)] with q hq
    exact heatGaussian_eq_zero_of_nonpos hn hq.le q.2
  · apply heatGaussian_contDiffAt_of_space_ne_zero hn
    intro hx
    exact hp (Prod.ext ht hx)
  · exact heatGaussian_contDiffAt ht

end PDE
