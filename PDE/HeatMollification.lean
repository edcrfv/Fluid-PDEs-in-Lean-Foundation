import PDE.HeatDistribution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Smooth convolution and the heat operator

These lemmas move derivatives to a compact smooth convolution kernel. They are
ingredients for local mollification, not an interior regularity theorem.
-/

open MeasureTheory Set
open scoped ContDiff BigOperators Convolution

namespace PDE

/-- A compactly localized representative, extended by zero outside the compact set. -/
noncomputable def heatLocalization {d : ℕ} (K : Set (Space d))
    (u : Space d → ℝ) : Space d → ℝ := K.indicator u

theorem integrable_heatLocalization {n : ℕ} {Q K : Set (Space (n + 1))}
    {u : Space (n + 1) → ℝ} (hu : IsDistributionalHeatSolution Q u)
    (hK : IsCompact K) (hKQ : K ⊆ Q) : Integrable (heatLocalization K u) volume :=
  (integrable_indicator_iff hK.measurableSet).mpr
    (hu.locallyIntegrable.integrableOn_compact_subset hKQ hK)

theorem IsDistributionalHeatSolution.localize {n : ℕ}
    {Q K : Set (Space (n + 1))} {u : Space (n + 1) → ℝ}
    (hu : IsDistributionalHeatSolution Q u) (hKQ : K ⊆ Q) :
    IsDistributionalHeatSolution (interior K) (heatLocalization K u) := by
  apply (hu.mono (interior_subset.trans hKQ)).congr
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with z hz
  exact (Set.indicator_of_mem (interior_subset hz) u).symm

noncomputable def heatConvolution {d : ℕ} (u ρ : Space d → ℝ) : Space d → ℝ :=
  u ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ

theorem heatConvolution_contDiff {d : ℕ} {u ρ : Space d → ℝ}
    (hu : LocallyIntegrable u volume) (hρ : ContDiff ℝ ∞ ρ)
    (hc : HasCompactSupport ρ) : ContDiff ℝ ∞ (heatConvolution u ρ) :=
  hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hu hρ

theorem coordDeriv_heatConvolution {d : ℕ} {u ρ : Space d → ℝ}
    (hu : LocallyIntegrable u volume) (hρ : ContDiff ℝ ∞ ρ)
    (hc : HasCompactSupport ρ) (i : Fin d) :
    coordDeriv i (heatConvolution u ρ) = heatConvolution u (coordDeriv i ρ) := by
  funext x
  have hd := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    hu (hρ.of_le (by simp)) x
  have hi := (hc.fderiv ℝ).convolutionExists_right
    ((ContinuousLinearMap.mul ℝ ℝ).precompR (Space d)) hu
    (hρ.continuous_fderiv (by simp)) x
  change (fderiv ℝ (u ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) x)
    (Pi.single i 1) = _
  rw [hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hi]
  rfl

theorem coordDeriv_twice_heatConvolution {d : ℕ} {u ρ : Space d → ℝ}
    (hu : LocallyIntegrable u volume) (hρ : ContDiff ℝ ∞ ρ)
    (hc : HasCompactSupport ρ) (i j : Fin d) :
    coordDeriv i (coordDeriv j (heatConvolution u ρ)) =
      heatConvolution u (coordDeriv i (coordDeriv j ρ)) := by
  rw [coordDeriv_heatConvolution hu hρ hc j]
  exact coordDeriv_heatConvolution hu
    ((hρ.fderiv_right (by simp)).clm_apply contDiff_const)
    (hc.fderiv_apply ℝ (Pi.single j 1)) i

/-- Reflecting and translating a test kernel reverses a first coordinate derivative. -/
theorem coordDeriv_reflectedTranslation {d : ℕ} {ρ : Space d → ℝ}
    (hρ : Differentiable ℝ ρ) (i : Fin d) (x y : Space d) :
    coordDeriv i (fun z => ρ (x - z)) y = -coordDeriv i ρ (x - y) := by
  have hd := (hρ (x - y)).hasFDerivAt.comp y
    ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
  simpa [coordDeriv, Function.comp_def] using
    congrArg (fun L => L (Pi.single i 1)) hd.fderiv

theorem coordDeriv_twice_reflectedTranslation {d : ℕ} {ρ : Space d → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (i : Fin d) (x y : Space d) :
    coordDeriv i (coordDeriv i (fun z => ρ (x - z))) y =
      coordDeriv i (coordDeriv i ρ) (x - y) := by
  have hfirst : coordDeriv i (fun z => ρ (x - z)) =
      fun z => -coordDeriv i ρ (x - z) :=
    funext (coordDeriv_reflectedTranslation (hρ.differentiable (by simp)) i x)
  rw [hfirst]
  have hs : ContDiff ℝ ∞ (coordDeriv i ρ) :=
    (hρ.fderiv_right (by simp)).clm_apply contDiff_const
  have hd : Differentiable ℝ (coordDeriv i ρ) := hs.differentiable (by simp)
  have hsecond := coordDeriv_reflectedTranslation hd i x y
  simpa only [coordDeriv, fderiv_fun_neg, neg_apply, neg_neg]
    using congrArg Neg.neg hsecond

theorem heatResidual_heatConvolution {n : ℕ} {u ρ : Space (n + 1) → ℝ}
    (hu : LocallyIntegrable u volume) (hρ : ContDiff ℝ ∞ ρ)
    (hc : HasCompactSupport ρ) (x : Space (n + 1)) :
    heatResidual (heatConvolution u ρ) x =
      ∫ y, u y * heatResidual ρ (x - y) := by
  have hd (i : Fin (n + 1)) : ContDiff ℝ ∞ (coordDeriv i ρ) :=
    (hρ.fderiv_right (by simp)).clm_apply contDiff_const
  have ht : Integrable (fun y => u y * coordDeriv 0 ρ (x - y)) volume :=
    (hc.fderiv_apply ℝ (Pi.single 0 1)).convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℝ) hu (hd 0).continuous x
  have hi (i : Fin n) :
      Integrable (fun y => u y * coordDeriv i.succ (coordDeriv i.succ ρ) (x - y))
        volume :=
    ((hc.fderiv_apply ℝ (Pi.single i.succ 1)).fderiv_apply ℝ
      (Pi.single i.succ 1)).convolutionExists_right
        (ContinuousLinearMap.mul ℝ ℝ) hu
          (((hd i.succ).continuous_fderiv (by simp)).clm_apply continuous_const) x
  simp only [heatResidual, spaceTimeLaplacian]
  simp_rw [coordDeriv_twice_heatConvolution hu hρ hc]
  rw [coordDeriv_heatConvolution hu hρ hc 0]
  change (∫ y, u y * coordDeriv 0 ρ (x - y)) -
    (∑ i : Fin n, ∫ y, u y * coordDeriv i.succ (coordDeriv i.succ ρ) (x - y)) = _
  rw [← integral_finsetSum _ (fun i _ => hi i),
    ← integral_sub ht (integrable_finsetSum _ (fun i _ => hi i))]
  apply integral_congr_ae
  filter_upwards with y
  simp only [mul_sub, Finset.mul_sum]

/-- A reflected translated kernel is an admissible test precisely where its
support lies inside the domain. -/
theorem heatKernel_testFunction {d : ℕ} {Q : Set (Space d)} {ρ : Space d → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ) (x : Space d)
    (hx : tsupport (fun y => ρ (x - y)) ⊆ Q) :
    IsTestFunctionOn Q (fun y => ρ (x - y)) :=
  ⟨hρ.comp (contDiff_const.sub contDiff_id),
    hc.comp_homeomorph (Homeomorph.subLeft x), hx⟩

/-- Smoothing preserves the heat equation at every point whose translated
kernel is supported inside the weak-solution domain. Global local integrability
is an explicit hypothesis, to be obtained from localization for a general input. -/
theorem IsDistributionalHeatSolution.heatConvolution_eq {n : ℕ}
    {Q : Set (Space (n + 1))} {u ρ : Space (n + 1) → ℝ}
    (hu : IsDistributionalHeatSolution Q u) (hl : LocallyIntegrable u volume)
    (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ) (x : Space (n + 1))
    (hx : tsupport (fun y => ρ (x - y)) ⊆ Q) :
    coordDeriv 0 (heatConvolution u ρ) x =
      spaceTimeLaplacian (heatConvolution u ρ) x := by
  have ht := heatKernel_testFunction hρ hc x hx
  have heq := hu.equation_global ht
  have hop (y : Space (n + 1)) :
      heatAdjointTest (fun z => ρ (x - z)) y = -heatResidual ρ (x - y) := by
    simp only [heatAdjointTest, spaceTimeLaplacian,
      coordDeriv_reflectedTranslation (hρ.differentiable (by simp)),
      coordDeriv_twice_reflectedTranslation hρ, heatResidual]
    ring
  simp only [hop, mul_neg, integral_neg, neg_eq_zero] at heq
  have hz : heatResidual (heatConvolution u ρ) x = 0 :=
    (heatResidual_heatConvolution hl hρ hc x).trans heq
  exact sub_eq_zero.mp hz

/-- Every compact localization of a weak solution has a smooth convolution
satisfying the heat equation wherever the translated kernel stays in the
interior of the localization set. No global integrability of the original input
is required. -/
theorem IsDistributionalHeatSolution.localized_heatConvolution {n : ℕ}
    {Q K : Set (Space (n + 1))} {u ρ : Space (n + 1) → ℝ}
    (hu : IsDistributionalHeatSolution Q u) (hK : IsCompact K) (hKQ : K ⊆ Q)
    (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ) :
    ContDiff ℝ ∞ (heatConvolution (heatLocalization K u) ρ) ∧
      ∀ x, tsupport (fun y => ρ (x - y)) ⊆ interior K →
        coordDeriv 0 (heatConvolution (heatLocalization K u) ρ) x =
          spaceTimeLaplacian (heatConvolution (heatLocalization K u) ρ) x := by
  have hi := (integrable_heatLocalization hu hK hKQ).locallyIntegrable
  exact ⟨heatConvolution_contDiff hi hρ hc,
    fun x hx => (hu.localize hKQ).heatConvolution_eq hi hρ hc x hx⟩

end PDE
