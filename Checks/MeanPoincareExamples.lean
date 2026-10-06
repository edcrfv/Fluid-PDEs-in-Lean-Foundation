import PDE.CubePoincare
import PDE.WeakIntervalPoincare

/-! Nonzero boundary values and all three coordinate derivatives in the cube API. -/

open PDE MeasureTheory Set
open scoped ENNReal

private def affineCube (z : ℝ × (ℝ × ℝ)) : ℝ := 7 + z.1 + 2 * z.2.1 + 3 * z.2.2

private theorem affineCube_dx (z : ℝ × (ℝ × ℝ)) :
    deriv (fun t => affineCube (t, z.2)) z.1 = 1 := by
  simp [affineCube, deriv_add_const]

private theorem affineCube_dy (z : ℝ × (ℝ × ℝ)) :
    deriv (fun t => affineCube (z.1, t, z.2.2)) z.2.1 = 2 := by
  simp [affineCube, deriv_add_const, deriv_const_add]

private theorem affineCube_dz (z : ℝ × (ℝ × ℝ)) :
    deriv (fun t => affineCube (z.1, z.2.1, t)) z.2.2 = 3 := by
  simp [affineCube, deriv_const_add]

-- All three derivative energies contribute; the affine function never has zero
-- boundary trace on the cube. The mean is not specified as extra input.
example :
    (∫ z, (affineCube z - ∫ w, affineCube w ∂unitCubeMeasure) ^ 2 ∂unitCubeMeasure) ≤ 14 := by
  have hf : MemLp affineCube 2 unitCubeMeasure := by
    rw [unitCubeMeasure_eq_volume_restrict]
    have hc : Continuous affineCube := by unfold affineCube; fun_prop
    apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
    exact (hc.pow 2).continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have hdx : MemLp (fun z => deriv (fun t => affineCube (t, z.2)) z.1) 2 unitCubeMeasure := by
    simpa only [affineCube_dx] using (memLp_const (1 : ℝ) :
      MemLp (fun _ : ℝ × (ℝ × ℝ) => (1 : ℝ)) 2 unitCubeMeasure)
  have hdy : MemLp (fun z => deriv (fun t => affineCube (z.1, t, z.2.2)) z.2.1) 2 unitCubeMeasure := by
    simpa only [affineCube_dy] using (memLp_const (2 : ℝ) :
      MemLp (fun _ : ℝ × (ℝ × ℝ) => (2 : ℝ)) 2 unitCubeMeasure)
  have hdz : MemLp (fun z => deriv (fun t => affineCube (z.1, z.2.1, t)) z.2.2) 2 unitCubeMeasure := by
    simpa only [affineCube_dz] using (memLp_const (3 : ℝ) :
      MemLp (fun _ : ℝ × (ℝ × ℝ) => (3 : ℝ)) 2 unitCubeMeasure)
  have hx : ∀ᵐ y ∂unitSquareMeasure,
      AbsolutelyContinuousOnInterval (fun t => affineCube (t, y)) 0 1 := by
    filter_upwards with y
    apply ContDiffOn.absolutelyContinuousOnInterval
    unfold affineCube
    fun_prop
  have hy : ∀ᵐ x ∂unitIntervalMeasure, ∀ᵐ z ∂unitIntervalMeasure,
      AbsolutelyContinuousOnInterval (fun t => affineCube (x, t, z)) 0 1 := by
    filter_upwards with x
    filter_upwards with z
    apply ContDiffOn.absolutelyContinuousOnInterval
    unfold affineCube
    fun_prop
  have hz : ∀ᵐ x ∂unitIntervalMeasure, ∀ᵐ y ∂unitIntervalMeasure,
      AbsolutelyContinuousOnInterval (fun t => affineCube (x, y, t)) 0 1 := by
    filter_upwards with x
    filter_upwards with y
    apply ContDiffOn.absolutelyContinuousOnInterval
    unfold affineCube
    fun_prop
  have h := unitCube_mean_poincare hf hdx hdy hdz hx hy hz
  simpa only [affineCube_dx, affineCube_dy, affineCube_dz,
    show (1 : ℝ) ^ 2 + 2 ^ 2 + 3 ^ 2 = 14 by norm_num,
    integral_const, probReal_univ, one_smul] using h

-- Removing the mean would give a false inequality even for a constant function:
-- the derivative energy is zero but the L² norm is seven.
example : lpNorm (fun _ : ℝ × (ℝ × ℝ) => (7 : ℝ)) 2 unitCubeMeasure = 7 := by
  rw [PDE.lpNorm_two_eq_sqrt_integral_sq (memLp_const _)]
  norm_num [Real.sqrt_eq_iff_eq_sq]
