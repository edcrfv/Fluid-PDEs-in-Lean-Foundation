import PDE.IntervalTestFunctions
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-! Positivity from nonnegative compact smooth tests on a finite interval.
Normalized bump convolution and Lebesgue differentiation recover the a.e.
inequality; no pointwise continuity of the tested function is assumed. -/

open MeasureTheory Set Filter Metric
open scoped ContDiff Topology Convolution

namespace PDE

private noncomputable def shrinkingBump (j : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1), by positivity, by
    have hp : 0 < 1 / ((j : ℝ) + 1) := by positivity
    linarith⟩

/-- Nonnegative distributional action on every nonnegative compact smooth
test implies a.e. nonnegativity, including the endpoints up to null sets. -/
theorem ae_nonneg_of_interval_smooth_tests {a b : ℝ} {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc a b))
    (htest : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Ioo a b → (∀ x, 0 ≤ g x) → 0 ≤ ∫ x in Icc a b, g x * f x) :
    ∀ᵐ x ∂volume.restrict (Icc a b), 0 ≤ f x := by
  let F := (Icc a b).indicator f
  have hFi : Integrable F := (integrable_indicator_iff measurableSet_Icc).mpr hf
  have hrad : Tendsto (fun j => (shrinkingBump j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hratio : ∀ᶠ j in atTop, (shrinkingBump j).rOut ≤ 2 * (shrinkingBump j).rIn :=
    Eventually.of_forall fun j => by dsimp [shrinkingBump]; linarith
  have hconv := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := volume) hrad hratio hFi.locallyIntegrable
  have hout : ∀ᵐ x ∂volume.restrict (Ioo a b), 0 ≤ f x := by
    filter_upwards [ae_restrict_of_ae hconv, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    have hsmall : ∀ᶠ j in atTop, (shrinkingBump j).rOut < min (x - a) (b - x) :=
      (tendsto_order.mp hrad).2 _ (lt_min (by linarith [hxI.1]) (by linarith [hxI.2]))
    have hn : ∀ᶠ j in atTop,
        0 ≤ ((shrinkingBump j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) x := by
      filter_upwards [hsmall] with j hj
      let g := fun y => (shrinkingBump j).normed volume (x - y)
      have hgs : ContDiff ℝ ∞ g := (shrinkingBump j).contDiff_normed.comp
        (contDiff_const.sub contDiff_id)
      have hball : tsupport g ⊆ closedBall x (shrinkingBump j).rOut := by
        intro y hy
        have hh := tsupport_comp_subset_preimage ((shrinkingBump j).normed volume)
          (continuous_const.sub continuous_id) hy
        change x - y ∈ tsupport ((shrinkingBump j).normed volume) at hh
        rw [(shrinkingBump j).tsupport_normed_eq, mem_closedBall, dist_zero_right] at hh
        simpa only [mem_closedBall, Real.dist_eq, Real.norm_eq_abs, abs_sub_comm] using hh
      have hgc : HasCompactSupport g :=
        (isCompact_closedBall x (shrinkingBump j).rOut).of_isClosed_subset (isClosed_tsupport g) hball
      have hgI : tsupport g ⊆ Ioo a b := by
        intro y hy
        have hb := hball hy
        rw [Real.closedBall_eq_Icc] at hb
        constructor <;> linarith [(lt_min_iff.mp hj).1, (lt_min_iff.mp hj).2, hb.1, hb.2]
      have hpos := htest g hgs hgc hgI
        (fun y => (shrinkingBump j).nonneg_normed (μ := volume) (x - y))
      rw [convolution_eq_swap]
      change 0 ≤ ∫ y, g y * F y
      have he : (fun y => g y * F y) = (Icc a b).indicator (fun y => g y * f y) := by
        funext y
        by_cases hy : y ∈ Icc a b <;> simp [F, hy]
      rw [he, integral_indicator measurableSet_Icc]
      exact hpos
    have hnonneg := ge_of_tendsto hx hn
    simpa only [F, indicator_of_mem (Ioo_subset_Icc_self hxI)] using hnonneg
  rwa [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hout

end PDE
