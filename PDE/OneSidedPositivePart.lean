import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Smooth convex approximation of the positive part from below. Its slope is
exactly zero on the nonpositive half-line, including the threshold. This avoids
the tails and threshold half-weight of symmetric square-root rounding. -/

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace PDE

noncomputable def oneSidedSlope (δ s : ℝ) : ℝ := Real.smoothTransition (s / δ)

noncomputable def oneSidedCurvature (δ s : ℝ) : ℝ := deriv (oneSidedSlope δ) s

noncomputable def oneSidedPositivePart (δ s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, oneSidedSlope δ t

theorem contDiff_oneSidedSlope (δ : ℝ) : ContDiff ℝ ∞ (oneSidedSlope δ) :=
  Real.smoothTransition.contDiff.comp (contDiff_id.div_const δ)

theorem oneSidedSlope_bounds (δ s : ℝ) : 0 ≤ oneSidedSlope δ s ∧ oneSidedSlope δ s ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem oneSidedSlope_zero {δ s : ℝ} (hδ : 0 < δ) (hs : s ≤ 0) :
    oneSidedSlope δ s = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hs hδ.le)

theorem oneSidedSlope_one {δ s : ℝ} (hδ : 0 < δ) (hs : δ ≤ s) :
    oneSidedSlope δ s = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div hδ).mpr hs)

theorem oneSidedCurvature_nonneg {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    0 ≤ oneSidedCurvature δ s := by
  apply Monotone.deriv_nonneg
  intro x y hxy
  exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right hxy hδ.le)

theorem hasDerivAt_oneSidedPositivePart (δ s : ℝ) :
    HasDerivAt (oneSidedPositivePart δ) (oneSidedSlope δ s) s := by
  have hc := (contDiff_oneSidedSlope δ).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

theorem hasDerivAt_oneSidedSlope (δ s : ℝ) :
    HasDerivAt (oneSidedSlope δ) (oneSidedCurvature δ s) s :=
  ((contDiff_oneSidedSlope δ).differentiable (by simp) s).hasDerivAt

theorem contDiff_oneSidedPositivePart (δ : ℝ) : ContDiff ℝ ∞ (oneSidedPositivePart δ) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun s => (hasDerivAt_oneSidedPositivePart δ s).differentiableAt, ?_⟩
  have he : deriv (oneSidedPositivePart δ) = oneSidedSlope δ :=
    funext fun s => (hasDerivAt_oneSidedPositivePart δ s).deriv
  rw [he]
  exact contDiff_oneSidedSlope δ

theorem oneSidedPositivePart_zero {δ s : ℝ} (hδ : 0 < δ) (hs : s ≤ 0) :
    oneSidedPositivePart δ s = 0 := by
  unfold oneSidedPositivePart
  calc
    _ = ∫ _t in (0 : ℝ)..s, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_ge hs] at ht
      exact oneSidedSlope_zero hδ ht.2
    _ = 0 := by simp

theorem oneSidedPositivePart_nonneg {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    0 ≤ oneSidedPositivePart δ s := by
  by_cases hs : s ≤ 0
  · rw [oneSidedPositivePart_zero hδ hs]
  · exact intervalIntegral.integral_nonneg (le_of_not_ge hs)
      (fun t _ => (oneSidedSlope_bounds δ t).1)

/-- Uniform approximation from below, with error at most δ. -/
theorem oneSidedPositivePart_error {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    0 ≤ max s 0 - oneSidedPositivePart δ s ∧
      max s 0 - oneSidedPositivePart δ s ≤ δ := by
  by_cases hs : s ≤ 0
  · rw [oneSidedPositivePart_zero hδ hs, max_eq_right hs, sub_self]
    exact ⟨le_rfl, hδ.le⟩
  have hs0 : 0 ≤ s := (lt_of_not_ge hs).le
  rw [max_eq_left hs0]
  have hc := (contDiff_oneSidedSlope δ).continuous
  have hu : oneSidedPositivePart δ s ≤ s := by
    change (∫ t in (0 : ℝ)..s, oneSidedSlope δ t) ≤ s
    have h := intervalIntegral.integral_mono_on (μ := volume) hs0 (hc.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) (fun t _ => (oneSidedSlope_bounds δ t).2)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] using h
  refine ⟨sub_nonneg.mpr hu, ?_⟩
  by_cases hsd : s ≤ δ
  · linarith [oneSidedPositivePart_nonneg hδ s]
  · have hds : δ ≤ s := (lt_of_not_ge hsd).le
    have hi : (∫ t in δ..s, oneSidedSlope δ t) = s - δ := by
      calc
        _ = ∫ _t in δ..s, (1 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hds] at ht
          exact oneSidedSlope_one hδ ht.1
        _ = s - δ := by simp
    have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc.intervalIntegrable 0 δ) (hc.intervalIntegrable δ s)
    change oneSidedPositivePart δ δ + (∫ t in δ..s, oneSidedSlope δ t) =
      oneSidedPositivePart δ s at he
    rw [hi] at he
    linarith [oneSidedPositivePart_nonneg hδ δ]

theorem tendsto_oneSidedPositivePart (s : ℝ) :
    Tendsto (fun δ => oneSidedPositivePart δ s) (𝓝[>] 0) (𝓝 (max s 0)) := by
  have hid : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using tendsto_const_nhds.sub hid) tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    linarith [(oneSidedPositivePart_error hδ s).2]
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    linarith [(oneSidedPositivePart_error hδ s).1]

/-- Unlike symmetric rounding, the derivative converges to zero at s=0. -/
theorem tendsto_oneSidedSlope (s : ℝ) :
    Tendsto (fun δ => oneSidedSlope δ s) (𝓝[>] 0) (𝓝 (if 0 < s then 1 else 0)) := by
  by_cases hs : 0 < s
  · rw [ite_eq_left hs]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      (nhdsWithin_le_nhds (Iio_mem_nhds hs))] with δ hδ hsmall
    exact (oneSidedSlope_one hδ hsmall.le).symm
  · rw [ite_eq_right hs]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (oneSidedSlope_zero hδ (le_of_not_gt hs)).symm

end PDE
