import PDE.SobolevCube
import PDE.CubeSobolevLimit

/-! Actual H¹ embeds into L⁶ on the open unit cube without a boundary trace
condition. The mean-zero inequality is derived, not supplied as a premise. -/

open MeasureTheory Set
open scoped ENNReal

namespace PDE

private theorem h1_cube_sub_const_estimate (u : H1 (unitOpenCube 3)) (c : ℝ) :
    eLpNorm (fun x => H1.value (unitOpenCube 3) u x - c) 6
      (volume.restrict (unitOpenCube 3)) ≤
    eLpNorm (fun x => H1.value (unitOpenCube 3) u x - c) 2
      (volume.restrict (unitOpenCube 3)) +
        4 * ∑ i : Fin 3, ‖H1.derivative (unitOpenCube 3) i u‖ₑ := by
  have hf := (Lp.stronglyMeasurable (H1.value (unitOpenCube 3) u)).measurable
  have hd (i : Fin 3) := (Lp.stronglyMeasurable (H1.derivative (unitOpenCube 3) i u)).measurable
  have hw (i : Fin 3) : ∀ᵐ x ∂volume.restrict (unitOpenCube 3),
      HasWeakDerivativeOnInterval 0 1
        (fun t => H1.value (unitOpenCube 3) u (Function.update x i t) - c)
        (fun t => H1.derivative (unitOpenCube 3) i u (Function.update x i t)) := by
    have hs := (u.hasWeakPartialOn i).ae_unitOpenCube_update_slices (Lp.memLp _) (Lp.memLp _)
    filter_upwards [hs] with x hx
    have h := hx.comp_contDiff (by norm_num) (contDiff_id.sub contDiff_const :
      ContDiff ℝ 1 (fun t : ℝ => t - c))
    simpa using h
  simpa only [← Lp.enorm_def, Pi.sub_def] using
    unitOpenCube_eLpNorm_six_le_of_weak_slices (hf.sub measurable_const) hd hw

/-- L⁶ membership of an arbitrary constant translate of an actual H¹
representative. It follows from weak derivatives and bounded approximation. -/
theorem H1.unitOpenCube_sub_const_memLp_six (u : H1 (unitOpenCube 3)) (c : ℝ) :
    MemLp (fun x => H1.value (unitOpenCube 3) u x - c) 6
      (volume.restrict (unitOpenCube 3)) := by
  have h2 : MemLp (fun x => H1.value (unitOpenCube 3) u x - c) 2
      (volume.restrict (unitOpenCube 3)) :=
    (Lp.memLp (H1.value (unitOpenCube 3) u)).sub (memLp_const c)
  refine ⟨h2.aestronglyMeasurable, (h1_cube_sub_const_estimate u c).trans_lt ?_⟩
  exact ENNReal.add_lt_top.mpr ⟨h2.eLpNorm_lt_top,
    ENNReal.mul_lt_top (by norm_num) (by
      simp only [Fin.sum_univ_three, ENNReal.add_lt_top]; exact ⟨⟨enorm_lt_top, enorm_lt_top⟩, enorm_lt_top⟩)⟩

/-- Actual H¹ on the open cube has L⁶ representatives; no zero trace or
preexisting L⁶ norm is assumed. -/
theorem H1.unitOpenCube_memLp_six (u : H1 (unitOpenCube 3)) :
    MemLp (H1.value (unitOpenCube 3) u) 6 (volume.restrict (unitOpenCube 3)) := by
  simpa only [sub_zero] using u.unitOpenCube_sub_const_memLp_six 0

/-- The nonzero-boundary Sobolev estimate, with its lower-order L² term. -/
theorem H1.unitOpenCube_sub_const_sobolev_six (u : H1 (unitOpenCube 3)) (c : ℝ) :
    lpNorm (fun x => H1.value (unitOpenCube 3) u x - c) 6
      (volume.restrict (unitOpenCube 3)) ≤
    lpNorm (fun x => H1.value (unitOpenCube 3) u x - c) 2
      (volume.restrict (unitOpenCube 3)) +
        4 * ∑ i : Fin 3, ‖H1.derivative (unitOpenCube 3) i u‖ := by
  have h2 : MemLp (fun x => H1.value (unitOpenCube 3) u x - c) 2
      (volume.restrict (unitOpenCube 3)) :=
    (Lp.memLp (H1.value (unitOpenCube 3) u)).sub (memLp_const c)
  have hs : (∑ i : Fin 3, ‖H1.derivative (unitOpenCube 3) i u‖ₑ) ≠ ∞ := by
    simp only [Fin.sum_univ_three, ENNReal.add_ne_top]
    exact ⟨⟨enorm_ne_top, enorm_ne_top⟩, enorm_ne_top⟩
  have hm : 4 * ∑ i : Fin 3, ‖H1.derivative (unitOpenCube 3) i u‖ₑ ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hs
  have h := ENNReal.toReal_mono
    (show eLpNorm (fun x => H1.value (unitOpenCube 3) u x - c) 2
      (volume.restrict (unitOpenCube 3)) +
        4 * ∑ i : Fin 3, ‖H1.derivative (unitOpenCube 3) i u‖ₑ ≠ ∞ by
      exact ENNReal.add_ne_top.mpr ⟨h2.eLpNorm_ne_top, hm⟩) (h1_cube_sub_const_estimate u c)
  simpa only [ENNReal.toReal_add h2.eLpNorm_ne_top hm,
    ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_sum (fun i _ => enorm_ne_top),
    toReal_enorm, toReal_eLpNorm h2.aestronglyMeasurable] using h

/-- Mean-zero L⁶ on actual H¹, with an explicit geometric constant 13.
The L⁶ membership and the L² mean Poincaré estimate have both been proved. -/
theorem H1.unitOpenCube_mean_sobolev_six (u : H1 (unitOpenCube 3)) :
    lpNorm (fun x => H1.value (unitOpenCube 3) u x -
      ∫ y in unitOpenCube 3, H1.value (unitOpenCube 3) u y) 6
        (volume.restrict (unitOpenCube 3)) ≤
      13 * Real.sqrt (∑ i : Fin 3, ‖H1.derivative (unitOpenCube 3) i u‖ ^ 2) := by
  let G := ∑ i : Fin 3, ‖H1.derivative (unitOpenCube 3) i u‖ ^ 2
  have hG : 0 ≤ G := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq := Real.sq_sqrt hG
  have hi (i : Fin 3) : ‖H1.derivative (unitOpenCube 3) i u‖ ^ 2 ≤ G :=
    Finset.single_le_sum (f := fun j : Fin 3 => ‖H1.derivative (unitOpenCube 3) j u‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hn (i : Fin 3) : ‖H1.derivative (unitOpenCube 3) i u‖ ≤ Real.sqrt G := by
    nlinarith [hi i, Real.sqrt_nonneg G, norm_nonneg (H1.derivative (unitOpenCube 3) i u)]
  have hp := u.unitOpenCube_mean_poincare_gradient
  simp only [probReal_univ, div_one] at hp
  have h := u.unitOpenCube_sub_const_sobolev_six
    (∫ y in unitOpenCube 3, H1.value (unitOpenCube 3) u y)
  change _ ≤ 13 * Real.sqrt G
  change _ ≤ Real.sqrt G at hp
  simp only [Fin.sum_univ_three] at h
  linarith [hn 0, hn 1, hn 2]

end PDE
