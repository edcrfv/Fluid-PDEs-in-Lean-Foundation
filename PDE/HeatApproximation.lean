import PDE.HeatMollification
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Local smooth caloric approximations

A concrete shrinking family of normalized smooth bumps gives smooth
approximations of a compact localization, converging almost everywhere.
At each interior point they eventually satisfy the heat equation.
Interior derivative estimates and passage of smoothness to the limit remain separate.
-/

open MeasureTheory Set Filter Metric
open scoped ContDiff BigOperators Convolution Topology

namespace PDE

noncomputable def heatMollifier (d k : ℕ) : ContDiffBump (0 : Space d) where
  rIn := 1 / ((k : ℝ) + 1)
  rOut := 2 / ((k : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply div_lt_div_of_pos_right (by norm_num)
    positivity

theorem heatMollifier_rOut_tendsto (d : ℕ) :
    Tendsto (fun k => (heatMollifier d k).rOut) atTop (𝓝 0) := by
  simpa [heatMollifier, div_eq_mul_inv] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2

noncomputable def heatApproximation {d : ℕ} (K : Set (Space d))
    (u : Space d → ℝ) (k : ℕ) : Space d → ℝ :=
  heatConvolution (heatLocalization K u) ((heatMollifier d k).normed volume)

theorem heatApproximation_contDiff {n : ℕ} {Q K : Set (Space (n + 1))}
    {u : Space (n + 1) → ℝ} (hu : IsDistributionalHeatSolution Q u)
    (hK : IsCompact K) (hKQ : K ⊆ Q) (k : ℕ) :
    ContDiff ℝ ∞ (heatApproximation K u k) :=
  heatConvolution_contDiff (integrable_heatLocalization hu hK hKQ).locallyIntegrable
    (heatMollifier (n + 1) k).contDiff_normed
    (heatMollifier (n + 1) k).hasCompactSupport_normed

theorem heatConvolution_swap {d : ℕ} (u ρ : Space d → ℝ) :
    heatConvolution u ρ = (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) := by
  funext x
  rw [heatConvolution, convolution_eq_swap, convolution_def]
  apply integral_congr_ae
  filter_upwards with y
  exact mul_comm _ _

theorem heatApproximation_ae_tendsto {n : ℕ} {Q K : Set (Space (n + 1))}
    {u : Space (n + 1) → ℝ} (hu : IsDistributionalHeatSolution Q u)
    (hK : IsCompact K) (hKQ : K ⊆ Q) :
    ∀ᵐ x ∂volume.restrict (interior K),
      Tendsto (fun k => heatApproximation K u k x) atTop (𝓝 (u x)) := by
  have hr : ∀ᶠ k in atTop,
      (heatMollifier (n + 1) k).rOut ≤ 2 * (heatMollifier (n + 1) k).rIn := by
    filter_upwards with k
    simp [heatMollifier, div_eq_mul_inv]
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (heatMollifier_rOut_tendsto (n + 1)) hr
    (integrable_heatLocalization hu hK hKQ).locallyIntegrable
  filter_upwards [ae_restrict_of_ae h, ae_restrict_mem isOpen_interior.measurableSet] with x hx hxin
  simpa only [heatApproximation, heatConvolution_swap, heatLocalization,
    Set.indicator_of_mem (interior_subset hxin)] using hx

theorem heatMollifier_eventually_supported {d : ℕ} {U : Set (Space d)}
    (hU : IsOpen U) {x : Space d} (hx : x ∈ U) :
    ∀ᶠ k in atTop,
      tsupport (fun y => (heatMollifier d k).normed volume (x - y)) ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  filter_upwards [(heatMollifier_rOut_tendsto d).eventually (gt_mem_nhds hε)] with k hk
  intro y hy
  have hy' := tsupport_comp_subset_preimage ((heatMollifier d k).normed volume)
    (continuous_const.sub continuous_id) hy
  rw [(heatMollifier d k).tsupport_normed_eq] at hy'
  change dist (x - y) 0 ≤ (heatMollifier d k).rOut at hy'
  have hd : dist y x ≤ (heatMollifier d k).rOut := by
    simpa only [dist_eq_norm_sub, sub_zero, norm_sub_rev] using hy'
  exact hball (lt_of_le_of_lt hd hk)

theorem heatApproximation_eventually_caloric {n : ℕ} {Q K : Set (Space (n + 1))}
    {u : Space (n + 1) → ℝ} (hu : IsDistributionalHeatSolution Q u)
    (hK : IsCompact K) (hKQ : K ⊆ Q) {x : Space (n + 1)} (hx : x ∈ interior K) :
    ∀ᶠ k in atTop, coordDeriv 0 (heatApproximation K u k) x =
      spaceTimeLaplacian (heatApproximation K u k) x := by
  filter_upwards [heatMollifier_eventually_supported isOpen_interior hx] with k hk
  exact (hu.localized_heatConvolution hK hKQ
    (heatMollifier (n + 1) k).contDiff_normed
    (heatMollifier (n + 1) k).hasCompactSupport_normed).2 x hk

end PDE
