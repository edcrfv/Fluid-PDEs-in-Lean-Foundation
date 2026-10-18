import PDE.HeatGaussianFundamental
import PDE.HeatMollification

/-!
# The heat kernel in coordinate space

Transport the Gaussian fundamental-solution identity from product coordinates to
`Space (n + 1)`, with coordinate zero as time. The coordinate equivalence preserves
Lebesgue measure. Local integrability and smoothness away from the source are
transported as well. Reflection of the test function gives a representation of
compactly supported smooth functions by their classical heat residual.
-/

open MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators

namespace PDE

private noncomputable def heatCoordinates (n : ℕ) : Space (n + 1) ≃L[ℝ] ℝ × Space n :=
  (Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)).symm

@[simp] private theorem heatCoordinates_apply {n : ℕ} (z : Space (n + 1)) :
    heatCoordinates n z = (z 0, fun i => z i.succ) := rfl

@[simp] private theorem heatCoordinates_symm_apply {n : ℕ} (p : ℝ × Space n) :
    (heatCoordinates n).symm p = Fin.cons p.1 p.2 := rfl

private theorem heatCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (heatCoordinates n) := by
  have hm := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  convert! hm using 1

private theorem integral_heatCoordinates {n : ℕ} (f : Space (n + 1) → ℝ) :
    (∫ z, f z) = ∫ p : ℝ × Space n, f (Fin.cons p.1 p.2) := by
  have hm := (heatCoordinates_measurePreserving n).symm
    (heatCoordinates n).toHomeomorph.toMeasurableEquiv
  exact (hm.integral_comp' f).symm

/-- The causal Gaussian in the coordinate convention of the distributional heat API. -/
noncomputable def heatSpaceTimeKernel {n : ℕ} (z : Space (n + 1)) : ℝ :=
  heatGaussian (z 0) (fun i => z i.succ)

private theorem fderiv_heatCoordinates_symm {n : ℕ} {φ : Space (n + 1) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (p v : ℝ × Space n) :
    fderiv ℝ (fun q => φ (Fin.cons q.1 q.2)) p v =
      fderiv ℝ φ (Fin.cons p.1 p.2) (Fin.cons v.1 v.2) := by
  have hd := ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp p
    (heatCoordinates n).symm.hasFDerivAt
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, heatCoordinates_symm_apply] using
    congrArg (fun L => L v) hd.fderiv

private theorem heatCoordinates_time_vector (n : ℕ) :
    (Fin.cons (1 : ℝ) (0 : Space n) : Space (n + 1)) = Pi.single (0 : Fin (n + 1)) 1 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

private theorem heatCoordinates_space_vector {n : ℕ} (i : Fin n) :
    (Fin.cons (0 : ℝ) (Pi.single i 1) : Space (n + 1)) = Pi.single i.succ 1 := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [Pi.single_apply]

/-- The product-coordinate adjoint agrees with the existing coordinate adjoint. -/
theorem heatProductAdjoint_cons {n : ℕ} {φ : Space (n + 1) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (p : ℝ × Space n) :
    heatProductAdjoint (fun q => φ (Fin.cons q.1 q.2)) p =
      heatAdjointTest φ (Fin.cons p.1 p.2) := by
  simp only [heatProductAdjoint, heatAdjointTest, spaceTimeLaplacian]
  rw [fderiv_heatCoordinates_symm hφ p (1, 0), heatCoordinates_time_vector]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun q : ℝ × Space n =>
      fderiv ℝ (fun r => φ (Fin.cons r.1 r.2)) q (0, Pi.single i 1)) =
      (fun q => coordDeriv i.succ φ (Fin.cons q.1 q.2)) := by
    ext q
    rw [fderiv_heatCoordinates_symm hφ q (0, Pi.single i 1), heatCoordinates_space_vector]
    rfl
  have hs : ContDiff ℝ ∞ (coordDeriv i.succ φ) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  rw [he, fderiv_heatCoordinates_symm (φ := coordDeriv i.succ φ) hs p (0, Pi.single i 1),
    heatCoordinates_space_vector]
  rfl

/-- The Gaussian fundamental-solution identity in the repository's coordinates. -/
theorem integral_heatSpaceTimeKernel_adjoint {n : ℕ} (hn : 0 < n)
    {φ : Space (n + 1) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ z, heatSpaceTimeKernel z * heatAdjointTest φ z) = -φ 0 := by
  have hs : ContDiff ℝ ∞ (fun p : ℝ × Space n => φ (Fin.cons p.1 p.2)) :=
    hφ.comp (heatCoordinates n).symm.contDiff
  have hcs : HasCompactSupport (fun p : ℝ × Space n => φ (Fin.cons p.1 p.2)) :=
    hc.comp_homeomorph (heatCoordinates n).symm.toHomeomorph
  have h := integral_heatGaussian_adjoint_volume hn hs hcs
  rw [integral_heatCoordinates]
  have hz : (Fin.cons (0 : ℝ) (0 : Space n) : Space (n + 1)) = 0 := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  simpa only [heatSpaceTimeKernel, Fin.cons_zero, Fin.cons_succ,
    heatProductAdjoint_cons hφ, hz] using h

/-- Local integrability of the causal kernel in the repository's coordinates. -/
theorem heatSpaceTimeKernel_locallyIntegrable {n : ℕ} (hn : 0 < n) :
    LocallyIntegrable (heatSpaceTimeKernel (n := n)) volume := by
  apply locallyIntegrable_iff.2
  intro K hK
  have hi := (heatGaussian_locallyIntegrable hn).integrableOn_isCompact
    (hK.image (heatCoordinates n).continuous)
  exact ((heatCoordinates_measurePreserving n).integrableOn_image
    (heatCoordinates n).toHomeomorph.toMeasurableEquiv.measurableEmbedding).mp hi

/-- The causal kernel is smooth away from its space–time source. -/
theorem heatSpaceTimeKernel_contDiffAt {n : ℕ} (hn : 0 < n)
    {z : Space (n + 1)} (hz : z ≠ 0) : ContDiffAt ℝ ∞ heatSpaceTimeKernel z := by
  have hp : heatCoordinates n z ≠ 0 := by
    intro h
    apply hz
    apply (heatCoordinates n).injective
    simpa only [map_zero] using h
  exact (heatGaussian_contDiffAt_off_origin hn hp).comp z (heatCoordinates n).contDiff.contDiffAt

/-- A compact smooth function is the convolution of the causal Gaussian with its
classical heat residual. -/
theorem heatSpaceTimeKernel_representation {n : ℕ} (hn : 0 < n)
    {v : Space (n + 1) → ℝ} (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (z : Space (n + 1)) :
    v z = ∫ y, heatSpaceTimeKernel y * heatResidual v (z - y) := by
  have h := integral_heatSpaceTimeKernel_adjoint hn
    (hv.comp (contDiff_const.sub contDiff_id))
    (hc.comp_homeomorph (Homeomorph.subLeft z))
  have he (y : Space (n + 1)) :
      heatAdjointTest (fun w => v (z - w)) y = -heatResidual v (z - y) := by
    simp only [heatAdjointTest, spaceTimeLaplacian,
      coordDeriv_reflectedTranslation (hv.differentiable (by simp)),
      coordDeriv_twice_reflectedTranslation hv, heatResidual]
    ring
  change (∫ y, heatSpaceTimeKernel y * heatAdjointTest (fun w => v (z - w)) y) =
    -v (z - 0) at h
  simpa only [he, mul_neg, integral_neg, sub_zero, neg_inj] using h.symm

end PDE
