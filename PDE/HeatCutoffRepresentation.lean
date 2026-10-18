import PDE.HeatGaussianCoordinates

/-!
# Local cutoff representation for smooth heat solutions

The product rule writes the residual of a cutoff times a smooth function in
spatial divergence form. Integration by parts transfers those spatial derivatives
to the Gaussian on the complement of its source. A cutoff constant near the
observation point ensures that the differentiated test supports avoid the source.

The resulting representation has no derivatives of the solution on its right-hand
side. It is proved for smooth functions satisfying the heat equation on the
cutoff's support. Applying it to weak solutions through local mollification and
strong L¹ convergence remains a separate step.
-/

open MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators

namespace PDE

private theorem contDiff_coord {d : ℕ} {f : Space d → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin d) : ContDiff ℝ ∞ (coordDeriv i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

private theorem coordDeriv_twice_mul {d : ℕ} {f g : Space d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i : Fin d) (x : Space d) :
    coordDeriv i (coordDeriv i (fun y => f y * g y)) x =
      f x * coordDeriv i (coordDeriv i g) x +
      g x * coordDeriv i (coordDeriv i f) x + 2 * coordDeriv i f x * coordDeriv i g x := by
  have hf1 := hf.differentiable (by simp)
  have hg1 := hg.differentiable (by simp)
  have hf2 := (contDiff_coord hf i).differentiable (by simp)
  have hg2 := (contDiff_coord hg i).differentiable (by simp)
  have he : coordDeriv i (fun y => f y * g y) =
      fun y => f y * coordDeriv i g y + g y * coordDeriv i f y := by
    ext y
    exact coordDeriv_mul (hf1 y) (hg1 y) i
  rw [he, coordDeriv_add (f := fun y => f y * coordDeriv i g y)
    (g := fun y => g y * coordDeriv i f y) ((hf1 x).mul (hg2 x)) ((hg1 x).mul (hf2 x)) i,
    coordDeriv_mul (hf1 x) (hg2 x), coordDeriv_mul (hg1 x) (hf2 x)]
  ring

/-- The cutoff product formula, with spatial derivatives collected in divergence form. -/
theorem heatResidual_mul_divergence {n : ℕ} {χ u : Space (n + 1) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) (x : Space (n + 1)) :
    heatResidual (fun y => χ y * u y) x =
      χ x * heatResidual u x + u x * heatAdjointTest χ x -
        2 * ∑ i : Fin n, coordDeriv i.succ (fun y => u y * coordDeriv i.succ χ y) x := by
  simp only [heatResidual, heatAdjointTest, spaceTimeLaplacian,
    coordDeriv_twice_mul hχ hu,
    coordDeriv_mul (hχ.differentiable (by simp) x) (hu.differentiable (by simp) x)]
  simp_rw [coordDeriv_mul (hu.differentiable (by simp) x)
    ((contDiff_coord hχ _).differentiable (by simp) x)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring_nf
  rw [Finset.sum_mul]

/-- Move a spatial derivative from a test supported away from the kernel's source.
The reflected kernel is only required to be smooth off that source. -/
theorem integral_heatSpaceTimeKernel_coordDeriv {n : ℕ} (hn : 0 < n)
    {θ : Space (n + 1) → ℝ} (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    {z : Space (n + 1)} (hz : z ∉ tsupport θ) (i : Fin (n + 1)) :
    (∫ y, heatSpaceTimeKernel (z - y) * coordDeriv i θ y) =
      ∫ y, coordDeriv i heatSpaceTimeKernel (z - y) * θ y := by
  let U : Set (Space (n + 1)) := {z}ᶜ
  have hU : IsOpen U := isClosed_singleton.isOpen_compl
  have hs : tsupport θ ⊆ U := by
    intro y hy
    change y ∉ ({z} : Set (Space (n + 1)))
    simpa only [mem_singleton_iff] using (fun he : y = z => hz (he ▸ hy))
  have htest : IsTestFunctionOn U θ := ⟨hθ, hc, hs⟩
  have hk : ContDiffOn ℝ ∞ (fun y => heatSpaceTimeKernel (z - y)) U := by
    intro y hy
    have hne : z - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    exact ((heatSpaceTimeKernel_contDiffAt hn hne).comp y
      (contDiff_const.sub contDiff_id).contDiffAt).contDiffWithinAt
  have hb := (hasWeakPartialOn_of_contDiffOn hU i (hk.of_le (by simp))).integration_by_parts θ htest
  rw [setIntegral_mul_eq_integral_of_tsupport_subset _ _ (htest.coordDeriv i).tsupport_subset,
    setIntegral_mul_eq_integral_of_tsupport_subset _ _ htest.tsupport_subset] at hb
  rw [hb, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y = z
  · subst y
    simp [image_eq_zero_of_notMem_tsupport hz]
  · have hne : z - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    have hd := (heatSpaceTimeKernel_contDiffAt hn hne).differentiableAt (by simp)
    have hcderiv := hd.hasFDerivAt.comp y
      ((hasFDerivAt_const z y).sub (hasFDerivAt_id y))
    have he : coordDeriv i (fun w => heatSpaceTimeKernel (z - w)) y =
        -coordDeriv i heatSpaceTimeKernel (z - y) := by
      simpa [coordDeriv, Function.comp_def] using
        congrArg (fun L => L (Pi.single i 1)) hcderiv.fderiv
    rw [he]
    ring

private theorem integrable_heatKernel_reflected_test {n : ℕ} (hn : 0 < n)
    {θ : Space (n + 1) → ℝ} (hθ : Continuous θ) (hc : HasCompactSupport θ)
    (z : Space (n + 1)) : Integrable (fun y => heatSpaceTimeKernel (z - y) * θ y) := by
  have hi := hc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hθ
    (heatSpaceTimeKernel_locallyIntegrable hn) z
  simpa only [ConvolutionExistsAt, ContinuousLinearMap.mul_apply', mul_comm] using hi

private theorem coordDeriv_support_away {d : ℕ} {χ : Space d → ℝ} {z : Space d}
    (hχ : χ =ᶠ[𝓝 z] fun _ => 1) (i : Fin d) : z ∉ tsupport (coordDeriv i χ) := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  filter_upwards [hχ.fderiv (𝕜 := ℝ)] with y hy
  change fderiv ℝ χ y (Pi.single i 1) = 0
  rw [hy]
  simp

/-- Local cutoff representation of a smooth heat solution. All derivatives of the
solution have been transferred to the cutoff and the Gaussian. -/
theorem heat_cutoff_representation {n : ℕ} (hn : 0 < n)
    {χ u : Space (n + 1) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hu : ContDiff ℝ ∞ u) (hcal : ∀ y ∈ tsupport χ, heatResidual u y = 0)
    {z : Space (n + 1)} (hflat : χ =ᶠ[𝓝 z] fun _ => 1) :
    u z = (∫ y, heatSpaceTimeKernel (z - y) * (u y * heatAdjointTest χ y)) -
      2 * ∑ i : Fin n, ∫ y,
        coordDeriv i.succ heatSpaceTimeKernel (z - y) * (u y * coordDeriv i.succ χ y) := by
  have htest : IsTestFunctionOn univ χ := ⟨hχ, hc, subset_univ _⟩
  have hA : Integrable (fun y => heatSpaceTimeKernel (z - y) * (u y * heatAdjointTest χ y)) :=
    integrable_heatKernel_reflected_test hn (hu.continuous.mul htest.heatAdjointTest.contDiff.continuous)
      htest.heatAdjointTest.hasCompactSupport.mul_left z
  have hg (i : Fin n) : ContDiff ℝ ∞ (fun y => u y * coordDeriv i.succ χ y) :=
    hu.mul (contDiff_coord hχ i.succ)
  have hcg (i : Fin n) : HasCompactSupport (fun y => u y * coordDeriv i.succ χ y) :=
    (hc.fderiv_apply ℝ (Pi.single i.succ 1)).mul_left
  have hB (i : Fin n) : Integrable (fun y => heatSpaceTimeKernel (z - y) *
      coordDeriv i.succ (fun w => u w * coordDeriv i.succ χ w) y) :=
    integrable_heatKernel_reflected_test hn (contDiff_coord (hg i) i.succ).continuous
      ((hcg i).fderiv_apply ℝ (Pi.single i.succ 1)) z
  have hf (y : Space (n + 1)) : heatResidual (fun w => χ w * u w) y =
      u y * heatAdjointTest χ y -
        2 * ∑ i : Fin n, coordDeriv i.succ (fun w => u w * coordDeriv i.succ χ w) y := by
    rw [heatResidual_mul_divergence hχ hu]
    have hz : χ y * heatResidual u y = 0 := by
      by_cases hy : y ∈ tsupport χ
      · rw [hcal y hy, mul_zero]
      · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    rw [hz, zero_add]
  have hr : χ z * u z = ∫ y, heatSpaceTimeKernel y *
      heatResidual (fun w => χ w * u w) (z - y) :=
    heatSpaceTimeKernel_representation hn (hχ.mul hu) hc.mul_right z
  rw [hflat.self_of_nhds, one_mul] at hr
  calc
    u z = ∫ y, heatSpaceTimeKernel (z - y) * heatResidual (fun w => χ w * u w) y := by
      rw [hr]
      simpa only [sub_sub_cancel] using
        (integral_sub_left_eq_self (fun y => heatSpaceTimeKernel y *
          heatResidual (fun w => χ w * u w) (z - y)) volume z).symm
    _ = ∫ y, heatSpaceTimeKernel (z - y) * (u y * heatAdjointTest χ y) -
        2 * ∑ i : Fin n, heatSpaceTimeKernel (z - y) *
          coordDeriv i.succ (fun w => u w * coordDeriv i.succ χ w) y := by
      apply integral_congr_ae
      filter_upwards with y
      rw [hf, ← Finset.mul_sum]
      ring
    _ = (∫ y, heatSpaceTimeKernel (z - y) * (u y * heatAdjointTest χ y)) -
        2 * ∑ i : Fin n, ∫ y, heatSpaceTimeKernel (z - y) *
          coordDeriv i.succ (fun w => u w * coordDeriv i.succ χ w) y := by
      rw [integral_sub hA ((integrable_finsetSum _ (fun i _ => hB i)).const_mul 2),
        integral_const_mul, integral_finsetSum _ (fun i _ => hB i)]
    _ = _ := by
      congr 2
      apply Finset.sum_congr rfl
      intro i _
      apply integral_heatSpaceTimeKernel_coordDeriv hn (hg i) (hcg i)
      exact fun hz => coordDeriv_support_away hflat i.succ (tsupport_mul_subset_right hz)

end PDE
