import PDE.DerivativeLevelSets
import PDE.IntervalWeakChainRule
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! The positive-part chain rule for actual interval distributional derivatives.
The derivative on the zero level is justified, even when that level has positive
measure. Original representatives remain only a.e. defined. -/

open MeasureTheory Set Filter
open scoped Topology

namespace PDE

theorem hasDerivAt_abs_of_zero_derivative {f : ℝ → ℝ} {x : ℝ}
    (hf : HasDerivAt f 0 x) (hx : f x = 0) :
    HasDerivAt (fun t => |f t|) 0 x := by
  apply HasDerivAt.of_isLittleO
  simpa only [hx, sub_zero, smul_zero, Real.norm_eq_abs, abs_zero] using hf.isLittleO.norm_left

/-- The compatibility condition at the kink is essential pointwise. It holds
almost everywhere for a weak derivative by the level-set lemma below. -/
theorem hasDerivAt_positivePart {f : ℝ → ℝ} {x d : ℝ}
    (hf : HasDerivAt f d x) (hkink : f x = 0 → d = 0) :
    HasDerivAt (fun t => max (f t) 0) (if 0 < f x then d else 0) x := by
  rcases lt_trichotomy (f x) 0 with hn | hz | hp
  · rw [ite_eq_right (not_lt_of_ge hn.le)]
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [hf.continuousAt.eventually (gt_mem_nhds hn)] with t ht
    exact max_eq_right ht.le
  · have hd := hkink hz
    subst d
    have ha := hasDerivAt_abs_of_zero_derivative hf hz
    have h := (hf.add ha).div_const 2
    have he : (fun t => (f t + |f t|) / 2) = fun t => max (f t) 0 := by
      funext t
      rcases le_total 0 (f t) with ht | ht
      · rw [abs_of_nonneg ht, max_eq_left ht]; ring
      · rw [abs_of_nonpos ht, max_eq_right ht]; ring
    simpa only [Pi.add_def, he, add_zero, zero_div, ite_self] using h
  · rw [ite_eq_left hp]
    apply hf.congr_of_eventuallyEq
    filter_upwards [hf.continuousAt.eventually (lt_mem_nhds hp)] with t ht
    exact max_eq_left ht.le

theorem absolutelyContinuous_positivePart {a b : ℝ} {v : ℝ → ℝ}
    (hv : AbsolutelyContinuousOnInterval v a b) :
    AbsolutelyContinuousOnInterval (fun t => max (v t) 0) a b := by
  apply absolutelyContinuousOnInterval_of_dist_le hv
  intro x _ y _
  simpa only [Real.dist_eq] using abs_max_sub_max_le_abs (v x) (v y) 0

/-- A weak derivative is zero on every prescribed level, up to a null set.
This does not say the level set itself has measure zero. -/
theorem HasWeakDerivativeOnInterval.ae_zero_on_level {a b : ℝ} (hab : a < b)
    {u du : ℝ → ℝ} (hu : HasWeakDerivativeOnInterval a b u du) (c : ℝ) :
    ∀ᵐ t ∂volume.restrict (Icc a b), u t = c → du t = 0 := by
  obtain ⟨v, _hv, huv, hdv⟩ := hu.exists_absolutelyContinuous_representative hab
  filter_upwards [huv, hdv, ae_restrict_of_ae (ae_deriv_eq_zero_on_level v c)]
    with t ht hdt hlevel
  intro hc
  rw [← hdt]
  exact hlevel (ht.symm.trans hc)

/-- Nonsmooth truncation against the same compact-test weak derivative interface.
The derivative is selected as zero on u=0, justified by the preceding theorem. -/
theorem HasWeakDerivativeOnInterval.positivePart {a b : ℝ} (hab : a < b)
    {u du : ℝ → ℝ} (hu : HasWeakDerivativeOnInterval a b u du) :
    HasWeakDerivativeOnInterval a b (fun t => max (u t) 0)
      (fun t => if 0 < u t then du t else 0) := by
  obtain ⟨v, hv, huv, hdv⟩ := hu.exists_absolutelyContinuous_representative hab
  have hc := hasWeakDerivativeOnInterval_of_absolutelyContinuous hab (absolutelyContinuous_positivePart hv)
  apply hc.congr (huv.symm.mono fun _ ht => congrArg (fun z => max z 0) ht)
  filter_upwards [ae_restrict_of_ae hv.ae_differentiableAt,
    ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (ae_deriv_eq_zero_on_level v 0),
    huv, hdv] with t hdt hm hk ht hd
  have hvd := hdt (by simpa only [uIcc_of_le hab.le] using hm)
  have hder := (hasDerivAt_positivePart hvd.hasDerivAt hk).deriv
  simpa only [← ht, hd] using hder

end PDE
