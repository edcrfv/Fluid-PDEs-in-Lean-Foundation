import PDE.HeatApproximation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# L¹ convergence of local heat approximations

Normalized nonnegative convolution is an L¹ contraction. Combined with a.e.
convergence, a dominated-convergence argument gives strong L¹ convergence of the
localized approximations. On each compact subset of the localization interior,
one index works for the heat equation at every point of that subset.
These results do not assert convergence of derivatives or smoothness of the limit.
-/

open MeasureTheory Set Filter Metric
open scoped ContDiff BigOperators Convolution Topology
namespace PDE

theorem heatConvolution_integral_norm_le {d : ℕ} {u ρ : Space d → ℝ}
    (hu : Integrable u volume) (hρ : Integrable ρ volume)
    (hρ_nonneg : ∀ x, 0 ≤ ρ x) (hρ_mass : (∫ x, ρ x) = 1) :
    (∫ x, ‖heatConvolution u ρ x‖) ≤ ∫ x, ‖u x‖ := by
  have hi : Integrable (heatConvolution u ρ) volume :=
    hu.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hρ
  have hj : Integrable (heatConvolution (fun x => ‖u x‖) ρ) volume :=
    hu.norm.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hρ
  calc
    (∫ x, ‖heatConvolution u ρ x‖) ≤ ∫ x, heatConvolution (fun y => ‖u y‖) ρ x := by
      apply integral_mono_ae hi.norm hj
      filter_upwards with x
      change ‖∫ y, u y * ρ (x - y)‖ ≤ ∫ y, ‖u y‖ * ρ (x - y)
      calc
        _ ≤ ∫ y, ‖u y * ρ (x - y)‖ := norm_integral_le_integral_norm _
        _ = _ := by
          apply integral_congr_ae
          filter_upwards with y
          rw [norm_mul, Real.norm_of_nonneg (hρ_nonneg (x - y))]
    _ = ∫ x, ‖u x‖ := by
      change (∫ x, ((fun y => ‖u y‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) x) = _
      rw [integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hu.norm hρ, hρ_mass]
      simp

/-- A.e. convergence and an upper bound by the limiting L¹ norm imply L¹ convergence.
Apply dominated convergence to the nonnegative triangle-inequality defect
‖F k x‖ + ‖f x‖ - ‖F k x - f x‖, which is bounded by 2 * ‖f x‖. -/
theorem tendsto_integral_norm_sub_of_ae_of_norm_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} {F : ℕ → α → ℝ}
    (hf : Integrable f μ) (hF : ∀ k, Integrable (F k) μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun k => F k x) atTop (𝓝 (f x)))
    (hbound : ∀ k, (∫ x, ‖F k x‖ ∂μ) ≤ ∫ x, ‖f x‖ ∂μ) :
    Tendsto (fun k => ∫ x, ‖F k x - f x‖ ∂μ) atTop (𝓝 0) := by
  let G : ℕ → α → ℝ := fun k x => ‖F k x‖ + ‖f x‖ - ‖F k x - f x‖
  have hi (k : ℕ) : Integrable (G k) μ :=
    ((hF k).norm.add hf.norm).sub ((hF k).sub hf).norm
  have hnonneg (k : ℕ) (x : α) : 0 ≤ G k x := by
    dsimp only [G]
    linarith [norm_sub_le (F k x) (f x)]
  have hdom (k : ℕ) : ∀ᵐ x ∂μ, ‖G k x‖ ≤ 2 * ‖f x‖ := by
    filter_upwards with x
    rw [Real.norm_of_nonneg (hnonneg k x)]
    have htri : ‖F k x‖ ≤ ‖F k x - f x‖ + ‖f x‖ := by
      simpa using norm_add_le (F k x - f x) (f x)
    dsimp only [G]
    linarith
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun k => G k x) atTop (𝓝 (2 * ‖f x‖)) := by
    filter_upwards [hae] with x hx
    simpa [G, two_mul] using
      (hx.norm.add (tendsto_const_nhds (x := ‖f x‖))).sub
        ((hx.sub (tendsto_const_nhds (x := f x))).norm)
  have hI := tendsto_integral_of_dominated_convergence (fun x => 2 * ‖f x‖)
    (fun k => (hi k).aestronglyMeasurable) (hf.norm.const_mul 2) hdom hlim
  have hzero : Tendsto (fun k => 2 * (∫ x, ‖f x‖ ∂μ) - ∫ x, G k x ∂μ)
      atTop (𝓝 0) := by
    simpa only [integral_const_mul, sub_self] using
      ((tendsto_const_nhds (x := 2 * (∫ x, ‖f x‖ ∂μ))).sub hI)
  apply squeeze_zero (fun k => integral_nonneg (fun x => norm_nonneg _)) _ hzero
  intro k
  have heq : (∫ x, G k x ∂μ) =
      (∫ x, ‖F k x‖ ∂μ) + (∫ x, ‖f x‖ ∂μ) - ∫ x, ‖F k x - f x‖ ∂μ := by
    dsimp only [G]
    have hs := integral_sub ((hF k).norm.add hf.norm) ((hF k).sub hf).norm
    simp only [Pi.add_apply, Pi.sub_apply] at hs
    rw [hs, integral_add (hF k).norm hf.norm]
  linarith [hbound k]

theorem heatConvolution_normed_tendsto_L1 {d : ℕ} {u : Space d → ℝ}
    (hu : Integrable u volume) :
    Tendsto (fun k => ∫ x,
      ‖heatConvolution u ((heatMollifier d k).normed volume) x - u x‖)
      atTop (𝓝 0) := by
  apply tendsto_integral_norm_sub_of_ae_of_norm_bound hu
  · intro k
    exact hu.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
      (heatMollifier d k).integrable_normed
  · have hr : ∀ᶠ k in atTop,
        (heatMollifier d k).rOut ≤ 2 * (heatMollifier d k).rIn := by
      filter_upwards with k
      simp [heatMollifier, div_eq_mul_inv]
    simpa only [heatConvolution_swap] using
      ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
        (heatMollifier_rOut_tendsto d) hr hu.locallyIntegrable
  · intro k
    exact heatConvolution_integral_norm_le hu (heatMollifier d k).integrable_normed
      (heatMollifier d k).nonneg_normed (heatMollifier d k).integral_normed

theorem heatApproximation_tendsto_L1 {n : ℕ} {Q K : Set (Space (n + 1))}
    {u : Space (n + 1) → ℝ} (hu : IsDistributionalHeatSolution Q u)
    (hK : IsCompact K) (hKQ : K ⊆ Q) :
    Tendsto (fun k => ∫ x, ‖heatApproximation K u k x - heatLocalization K u x‖)
      atTop (𝓝 0) :=
  heatConvolution_normed_tendsto_L1 (integrable_heatLocalization hu hK hKQ)

theorem heatApproximation_integral_norm_le {n : ℕ} {Q K : Set (Space (n + 1))}
    {u : Space (n + 1) → ℝ} (hu : IsDistributionalHeatSolution Q u)
    (hK : IsCompact K) (hKQ : K ⊆ Q) (k : ℕ) :
    (∫ x, ‖heatApproximation K u k x‖) ≤ ∫ x in K, ‖u x‖ := by
  have h := heatConvolution_integral_norm_le (integrable_heatLocalization hu hK hKQ)
    (heatMollifier (n + 1) k).integrable_normed
    (heatMollifier (n + 1) k).nonneg_normed (heatMollifier (n + 1) k).integral_normed
  change (∫ x, ‖heatApproximation K u k x‖) ≤ ∫ x, ‖heatLocalization K u x‖ at h
  simpa only [heatLocalization, norm_indicator_eq_indicator_norm,
    integral_indicator hK.measurableSet] using h

theorem heatApproximation_tendsto_L1_on {n : ℕ} {Q K U : Set (Space (n + 1))}
    {u : Space (n + 1) → ℝ} (hu : IsDistributionalHeatSolution Q u)
    (hK : IsCompact K) (hKQ : K ⊆ Q) (hU : MeasurableSet U) (hUK : U ⊆ K) :
    Tendsto (fun k => ∫ x in U, ‖heatApproximation K u k x - u x‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun k => integral_nonneg (fun x => norm_nonneg _)) _
    (heatApproximation_tendsto_L1 hu hK hKQ)
  intro k
  have hi := integrable_heatLocalization hu hK hKQ
  have hj : Integrable (heatApproximation K u k) volume :=
    hi.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
      (heatMollifier (n + 1) k).integrable_normed
  have heq : (∫ x in U, ‖heatApproximation K u k x - u x‖) =
      ∫ x in U, ‖heatApproximation K u k x - heatLocalization K u x‖ := by
    apply setIntegral_congr_fun hU
    intro x hx
    change ‖heatApproximation K u k x - u x‖ =
      ‖heatApproximation K u k x - heatLocalization K u x‖
    rw [heatLocalization, Set.indicator_of_mem (hUK hx) u]
  rw [heq]
  exact setIntegral_le_integral (hj.sub hi).norm (Filter.Eventually.of_forall (fun x => norm_nonneg _))

theorem heatApproximation_eventually_caloric_on_compact {n : ℕ}
    {Q K A : Set (Space (n + 1))} {u : Space (n + 1) → ℝ}
    (hu : IsDistributionalHeatSolution Q u) (hK : IsCompact K) (hKQ : K ⊆ Q)
    (hA : IsCompact A) (hAK : A ⊆ interior K) :
    ∀ᶠ k in atTop, ∀ x ∈ A, coordDeriv 0 (heatApproximation K u k) x =
      spaceTimeLaplacian (heatApproximation K u k) x := by
  obtain ⟨ε, hε, hthick⟩ := hA.exists_thickening_subset_open isOpen_interior hAK
  filter_upwards [(heatMollifier_rOut_tendsto (n + 1)).eventually (gt_mem_nhds hε)] with k hk
  intro x hx
  apply (hu.localized_heatConvolution hK hKQ
    (heatMollifier (n + 1) k).contDiff_normed
    (heatMollifier (n + 1) k).hasCompactSupport_normed).2 x
  intro y hy
  have hy' := tsupport_comp_subset_preimage ((heatMollifier (n + 1) k).normed volume)
    (show Continuous (fun y : Space (n + 1) => x - y) from
      continuous_const.sub continuous_id) hy
  rw [(heatMollifier (n + 1) k).tsupport_normed_eq] at hy'
  change dist (x - y) 0 ≤ (heatMollifier (n + 1) k).rOut at hy'
  have hd : dist y x ≤ (heatMollifier (n + 1) k).rOut := by
    simpa only [dist_eq_norm_sub, sub_zero, norm_sub_rev] using hy'
  exact hthick (mem_thickening_iff.mpr ⟨x, hx, lt_of_le_of_lt hd hk⟩)

end PDE
