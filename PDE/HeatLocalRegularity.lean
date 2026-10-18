import PDE.HeatKernelExtension
import PDE.HeatApproximationL1
import PDE.MovingMultiplier

/-!
# Smooth local representatives of weak heat solutions

The cutoff representation uses fixed compact smooth kernels. Strong L¹ convergence
passes its right-hand side to the limit, while the almost-everywhere convergence
of the mollifications identifies that limit with the weak solution. Smooth
convolution then gives a globally smooth function representing the solution on
a neighborhood of each interior point. Only openness of the domain is needed.
-/

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff BigOperators

namespace PDE

private theorem tendsto_heatConvolution_mul_of_L1 {d : ℕ}
    {f : ℕ → Space d → ℝ} {g w ρ : Space d → ℝ}
    (hf : ∀ k, Integrable (f k)) (hg : Integrable g)
    (hw : Continuous w) (hcw : HasCompactSupport w) (hρ : Continuous ρ)
    (hL1 : Tendsto (fun k => ∫ y, ‖f k y - g y‖) atTop (𝓝 0)) (x : Space d) :
    Tendsto (fun k => heatConvolution (fun y => f k y * w y) ρ x) atTop
      (𝓝 (heatConvolution (fun y => g y * w y) ρ x)) := by
  have ha : Continuous (fun y => w y * ρ (x - y)) :=
    hw.mul (hρ.comp (continuous_const.sub continuous_id))
  have hca : HasCompactSupport (fun y => w y * ρ (x - y)) := hcw.mul_right
  obtain ⟨C, hC⟩ := hca.exists_bound_of_continuous ha
  have h := tendsto_integral_mul_of_L1_of_bounded_ae hf hg
    (fun _ => ha.aestronglyMeasurable)
    (fun _ => ae_of_all _ hC) hL1 (ae_of_all _ fun _ => tendsto_const_nhds)
  simpa only [heatConvolution, convolution_def, ContinuousLinearMap.mul_apply', mul_assoc] using h

private theorem contDiff_heatConvolution_mul {d : ℕ} {g w ρ : Space d → ℝ}
    (hg : Integrable g) (hw : Continuous w) (hcw : HasCompactSupport w)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) :
    ContDiff ℝ ∞ (heatConvolution (fun y => g y * w y) ρ) := by
  have hi : Integrable (fun y => g y * w y) :=
    hg.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hw hcw
  exact heatConvolution_contDiff hi.locallyIntegrable hρ hcρ

/-- A cutoff supported inside a compact localization produces a smooth local
representative of a distributional heat solution, by passing the cutoff formula
through strong L¹ convergence of its mollifications. -/
theorem IsDistributionalHeatSolution.exists_smooth_local_representative_of_cutoff
    {n : ℕ} (hn : 0 < n) {Q K : Set (Space (n + 1))} {u : Space (n + 1) → ℝ}
    (hu : IsDistributionalHeatSolution Q u) (hK : IsCompact K) (hKQ : K ⊆ Q)
    {χ : Space (n + 1) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχK : tsupport χ ⊆ interior K) {z : Space (n + 1)}
    (hflat : χ =ᶠ[𝓝 z] fun _ => 1) :
    ∃ (U : Set (Space (n + 1))) (v : Space (n + 1) → ℝ),
      IsOpen U ∧ z ∈ U ∧ U ⊆ interior K ∧ ContDiff ℝ ∞ v ∧
      u =ᵐ[volume.restrict U] v := by
  obtain ⟨U, ρ, σ, hU, hzU, hUχ, hρ, hcρ, hσ, hcσ, hrep⟩ :=
    exists_smooth_heat_cutoff_representation hn hχ hc hflat
  have hUK := hUχ.trans hχK
  let g := heatLocalization K u
  have hg : Integrable g := integrable_heatLocalization hu hK hKQ
  have hf (k : ℕ) : Integrable (heatApproximation K u k) :=
    hg.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
      (heatMollifier (n + 1) k).integrable_normed
  have ht : IsTestFunctionOn univ χ := ⟨hχ, hc, subset_univ _⟩
  let v : Space (n + 1) → ℝ := fun x =>
    heatConvolution (fun y => g y * heatAdjointTest χ y) ρ x -
      2 * ∑ i : Fin n, heatConvolution (fun y => g y * coordDeriv i.succ χ y) (σ i) x
  have hv : ContDiff ℝ ∞ v :=
    (contDiff_heatConvolution_mul hg ht.heatAdjointTest.contDiff.continuous
      ht.heatAdjointTest.hasCompactSupport hρ hcρ).sub
      (contDiff_const.mul (ContDiff.sum (fun i _ =>
        contDiff_heatConvolution_mul hg (ht.coordDeriv i.succ).contDiff.continuous
          (ht.coordDeriv i.succ).hasCompactSupport (hσ i) (hcσ i))))
  have hL1 := heatApproximation_tendsto_L1 hu hK hKQ
  have hcal := heatApproximation_eventually_caloric_on_compact hu hK hKQ hc.isCompact hχK
  have hlim (x : Space (n + 1)) (hx : x ∈ U) :
      Tendsto (fun k => heatApproximation K u k x) atTop (𝓝 (v x)) := by
    have h0 := tendsto_heatConvolution_mul_of_L1 hf hg
      ht.heatAdjointTest.contDiff.continuous ht.heatAdjointTest.hasCompactSupport hρ.continuous hL1 x
    have h1 (i : Fin n) := tendsto_heatConvolution_mul_of_L1 hf hg
      (ht.coordDeriv i.succ).contDiff.continuous (ht.coordDeriv i.succ).hasCompactSupport
      (hσ i).continuous hL1 x
    have hvlim := h0.sub ((tendsto_finsetSum Finset.univ (fun i _ => h1 i)).const_mul 2)
    apply hvlim.congr'
    filter_upwards [hcal] with k hk
    exact (hrep (heatApproximation K u k) (heatApproximation_contDiff hu hK hKQ k)
      (fun y hy => sub_eq_zero.mpr (hk y hy)) x hx).symm
  refine ⟨U, v, hU, hzU, hUK, hv, ?_⟩
  have hAE := ae_restrict_of_ae_restrict_of_subset hUK (heatApproximation_ae_tendsto hu hK hKQ)
  filter_upwards [hAE, ae_restrict_mem hU.measurableSet] with x hx hxU
  exact tendsto_nhds_unique hx (hlim x hxU)

/-- Every interior point of an open domain has a neighborhood on which the weak
heat solution agrees almost everywhere with a globally smooth function. -/
theorem IsDistributionalHeatSolution.exists_smooth_local_representative
    {n : ℕ} (hn : 0 < n) {Q : Set (Space (n + 1))} {u : Space (n + 1) → ℝ}
    (hu : IsDistributionalHeatSolution Q u) (hQ : IsOpen Q)
    {z : Space (n + 1)} (hz : z ∈ Q) :
    ∃ (U : Set (Space (n + 1))) (v : Space (n + 1) → ℝ),
      IsOpen U ∧ z ∈ U ∧ U ⊆ Q ∧ ContDiff ℝ ∞ v ∧ u =ᵐ[volume.restrict U] v := by
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp (hQ.mem_nhds hz)
  let K := closedBall z (r / 2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKQ : K ⊆ Q := (closedBall_subset_ball (half_lt_self hr)).trans hb
  let χ : ContDiffBump z :=
    { rIn := r / 8, rOut := r / 4, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  have hχK : tsupport χ ⊆ interior K := by
    rw [χ.tsupport_eq]
    apply (closedBall_subset_ball (show r / 4 < r / 2 by linarith)).trans
    exact isOpen_ball.subset_interior_iff.mpr ball_subset_closedBall
  obtain ⟨U, v, hU, hzU, hUK, hv, huv⟩ := hu.exists_smooth_local_representative_of_cutoff
    hn hK hKQ χ.contDiff χ.hasCompactSupport hχK χ.eventuallyEq_one
  exact ⟨U, v, hU, hzU, hUK.trans (interior_subset.trans hKQ), hv, huv⟩

end PDE
