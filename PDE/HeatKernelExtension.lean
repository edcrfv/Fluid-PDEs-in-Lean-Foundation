import PDE.HeatCutoffRepresentation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Smooth replacements for localized heat kernels

Cutting off near zero and at large distance produces compact smooth replacements
for functions smooth off the origin. Compact separation makes these replacements
valid on one neighborhood for all terms of the heat cutoff formula. This yields
a representation with fixed smooth convolution kernels, independently of the
smooth caloric input.
-/

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff BigOperators Pointwise

namespace PDE

/-- A function smooth away from zero has a compactly supported smooth replacement
on any compact set avoiding zero. -/
theorem exists_contDiff_compact_eqOn_away_zero {d : ℕ} {f : Space d → ℝ}
    (hf : ∀ x ≠ 0, ContDiffAt ℝ ∞ f x) {K : Set (Space d)}
    (hK : IsCompact K) (h0 : (0 : Space d) ∉ K) :
    ∃ ρ : Space d → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ EqOn ρ f K := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hK.isClosed.isOpen_compl.mem_nhds h0)
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  let a : ContDiffBump (0 : Space d) :=
    { rIn := r / 2, rOut := r, rIn_pos := half_pos hr, rIn_lt_rOut := half_lt_self hr }
  let b : ContDiffBump (0 : Space d) :=
    { rIn := R, rOut := R + 1, rIn_pos := hR, rIn_lt_rOut := by linarith }
  let ρ : Space d → ℝ := fun x => b x * ((1 - a x) * f x)
  refine ⟨ρ, ?_, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.2
    intro x
    by_cases hx : x = 0
    · subst x
      have hzero : ContDiffAt ℝ ∞ (fun _ : Space d => (0 : ℝ)) 0 := contDiffAt_const
      apply hzero.congr_of_eventuallyEq
      filter_upwards [a.eventuallyEq_one] with y hy
      simp [ρ, hy]
    · exact b.contDiff.contDiffAt.mul
        ((contDiffAt_const.sub a.contDiff.contDiffAt).mul (hf x hx))
  · exact b.hasCompactSupport.mul_right
  · intro x hx
    have ha : a x = 0 := by
      apply a.zero_of_le_dist
      change r ≤ dist x 0
      by_contra h
      exact hball (by simpa only [mem_ball] using lt_of_not_ge h) hx
    have hb : b x = 1 := by
      apply b.one_of_mem_closedBall
      simpa only [mem_closedBall, dist_zero_right] using hbound x hx
    simp [ρ, ha, hb]

/-- Simultaneously replace finitely many kernels smooth off zero by compact smooth
kernels near a point separated from the compact supports of their multipliers. -/
theorem exists_smooth_kernels_near_supports {d : ℕ} {ι : Type*} [Finite ι]
    {κ w : ι → Space d → ℝ} (hκ : ∀ i x, x ≠ 0 → ContDiffAt ℝ ∞ (κ i) x)
    (hw : ∀ i, HasCompactSupport (w i)) {z : Space d}
    (hz : ∀ i, z ∉ tsupport (w i)) :
    ∃ (U : Set (Space d)) (ρ : ι → Space d → ℝ),
      IsOpen U ∧ z ∈ U ∧ (∀ i, ContDiff ℝ ∞ (ρ i)) ∧
      (∀ i, HasCompactSupport (ρ i)) ∧
      ∀ i x, x ∈ U → ∀ y, κ i (x - y) * w i y = ρ i (x - y) * w i y := by
  let S := ⋃ i, tsupport (w i)
  have hS : IsCompact S := isCompact_iUnion (fun i => (hw i).isCompact)
  have hzS : z ∉ S := by simpa only [S, mem_iUnion, not_exists] using hz
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hS.isClosed.isOpen_compl.mem_nhds hzS)
  let K := closedBall z (r / 2) - S
  have hK : IsCompact K := by
    have he : K = (fun p : Space d × Space d => p.1 - p.2) ''
        (closedBall z (r / 2) ×ˢ S) := by
      ext q
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩
        exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
      · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
        exact ⟨x, hx, y, hy, rfl⟩
    rw [he]
    exact ((isCompact_closedBall z (r / 2)).prod hS).image (continuous_fst.sub continuous_snd)
  have h0 : (0 : Space d) ∉ K := by
    rintro ⟨x, hx, y, hy, hxy⟩
    have he : x = y := sub_eq_zero.mp hxy
    have hxS := hball (closedBall_subset_ball (half_lt_self hr) hx)
    exact hxS (he.symm ▸ hy)
  have hex (i : ι) := exists_contDiff_compact_eqOn_away_zero (hκ i) hK h0
  choose ρ hρ hcρ heq using hex
  refine ⟨ball z (r / 2), ρ, isOpen_ball, mem_ball_self (half_pos hr), hρ, hcρ, ?_⟩
  intro i x hx y
  by_cases hy : y ∈ tsupport (w i)
  · have hxy : x - y ∈ K :=
      ⟨x, ball_subset_closedBall hx, y, mem_iUnion_of_mem i hy, rfl⟩
    rw [heq i hxy]
  · simp only [image_eq_zero_of_notMem_tsupport hy, mul_zero]

private theorem eventuallyEq_coord_zero {d : ℕ} {f : Space d → ℝ} {z : Space d}
    {c : ℝ} (hf : f =ᶠ[𝓝 z] fun _ => c) (i : Fin d) :
    coordDeriv i f =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [hf.fderiv (𝕜 := ℝ)] with y hy
  change fderiv ℝ f y (Pi.single i 1) = 0
  rw [hy]
  simp

/-- Near a point where the cutoff equals one, its representation formula can use
fixed compact smooth kernels, independently of the smooth caloric input. -/
theorem exists_smooth_heat_cutoff_representation {n : ℕ} (hn : 0 < n)
    {χ : Space (n + 1) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {z : Space (n + 1)} (hflat : χ =ᶠ[𝓝 z] fun _ => 1) :
    ∃ (U : Set (Space (n + 1))) (ρ : Space (n + 1) → ℝ)
      (σ : Fin n → Space (n + 1) → ℝ),
      IsOpen U ∧ z ∈ U ∧ U ⊆ tsupport χ ∧
      ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      (∀ i, ContDiff ℝ ∞ (σ i)) ∧ (∀ i, HasCompactSupport (σ i)) ∧
      ∀ u : Space (n + 1) → ℝ, ContDiff ℝ ∞ u →
        (∀ y ∈ tsupport χ, heatResidual u y = 0) → ∀ x ∈ U,
        u x = heatConvolution (fun y => u y * heatAdjointTest χ y) ρ x -
          2 * ∑ i : Fin n, heatConvolution (fun y => u y * coordDeriv i.succ χ y) (σ i) x := by
  let w : Option (Fin n) → Space (n + 1) → ℝ :=
    fun i => i.elim (heatAdjointTest χ) (fun j => coordDeriv j.succ χ)
  let κ : Option (Fin n) → Space (n + 1) → ℝ :=
    fun i => i.elim heatSpaceTimeKernel (fun j => coordDeriv j.succ heatSpaceTimeKernel)
  have ht : IsTestFunctionOn univ χ := ⟨hχ, hc, subset_univ _⟩
  have hw : ∀ i, HasCompactSupport (w i) := by
    intro i
    cases i with
    | none => exact ht.heatAdjointTest.hasCompactSupport
    | some i => exact (ht.coordDeriv i.succ).hasCompactSupport
  have hk : ∀ i x, x ≠ 0 → ContDiffAt ℝ ∞ (κ i) x := by
    intro i x hx
    cases i with
    | none => exact heatSpaceTimeKernel_contDiffAt hn hx
    | some i =>
      exact ((heatSpaceTimeKernel_contDiffAt hn hx).fderiv_right (m := ∞) (by simp)).clm_apply
        contDiffAt_const
  have hz : ∀ i, z ∉ tsupport (w i) := by
    intro i
    apply notMem_tsupport_iff_eventuallyEq.mpr
    cases i with
    | some i => exact eventuallyEq_coord_zero hflat i.succ
    | none =>
      have h2 : ∀ᶠ y in 𝓝 z, ∀ i : Fin n,
          coordDeriv i.succ (coordDeriv i.succ χ) y = 0 :=
        eventually_all.2 (fun i => eventuallyEq_coord_zero
          (eventuallyEq_coord_zero hflat i.succ) i.succ)
      filter_upwards [eventuallyEq_coord_zero hflat 0, h2] with y hy hy2
      simp [w, heatAdjointTest, spaceTimeLaplacian, hy, hy2]
  obtain ⟨V, τ, hV, hzV, hτ, hcτ, heq⟩ := exists_smooth_kernels_near_supports hk hw hz
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hflat.eventuallyEq_nhds
  refine ⟨V ∩ ball z r, τ none, (fun i => τ (some i)), hV.inter isOpen_ball,
    ⟨hzV, mem_ball_self hr⟩, ?_, hτ none, hcτ none,
    (fun i => hτ (some i)), (fun i => hcτ (some i)), ?_⟩
  · intro x hx
    apply subset_tsupport χ
    change χ x ≠ 0
    rw [(hb hx.2).self_of_nhds]
    exact one_ne_zero
  · intro u hu hcal x hx
    have h := heat_cutoff_representation hn hχ hc hu hcal (hb hx.2)
    have h0 (y : Space (n + 1)) :
        heatSpaceTimeKernel (x - y) * (u y * heatAdjointTest χ y) =
          (u y * heatAdjointTest χ y) * τ none (x - y) := by
      have he := heq none x hx.1 y
      dsimp [κ, w] at he
      calc
        _ = u y * (heatSpaceTimeKernel (x - y) * heatAdjointTest χ y) := by ring
        _ = u y * (τ none (x - y) * heatAdjointTest χ y) := congrArg (u y * ·) he
        _ = _ := by ring
    have h1 (i : Fin n) (y : Space (n + 1)) :
        coordDeriv i.succ heatSpaceTimeKernel (x - y) * (u y * coordDeriv i.succ χ y) =
          (u y * coordDeriv i.succ χ y) * τ (some i) (x - y) := by
      have he := heq (some i) x hx.1 y
      dsimp [κ, w] at he
      calc
        _ = u y * (coordDeriv i.succ heatSpaceTimeKernel (x - y) * coordDeriv i.succ χ y) := by ring
        _ = u y * (τ (some i) (x - y) * coordDeriv i.succ χ y) := congrArg (u y * ·) he
        _ = _ := by ring
    simp_rw [h0, h1] at h
    simpa only [heatConvolution, convolution_def, ContinuousLinearMap.mul_apply'] using h

end PDE
