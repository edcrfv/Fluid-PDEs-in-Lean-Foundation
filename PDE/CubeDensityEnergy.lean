import PDE.SobolevCubeSix
import PDE.WeightedEnergyReal
import PDE.SpatialH1Family

/-! Mixed density L²(time; L⁶(space)) control from actual cube weak derivatives.
The cube has no zero-trace restriction. -/

open MeasureTheory
open scoped ENNReal

namespace PDE

theorem H1.unitOpenCube_six_squared_le (v : H1 (unitOpenCube 3)) {R : ℝ}
    (hR : 0 ≤ R)
    (hL2 : lpNorm (H1.value (unitOpenCube 3) v) 2 (volume.restrict (unitOpenCube 3)) ≤ R) :
    (∫⁻ x in unitOpenCube 3, ENNReal.ofReal |H1.value (unitOpenCube 3) v x| ^ (6 : ℝ)) ^
        (1 / 3 : ℝ) ≤ ENNReal.ofReal (2 * R ^ 2) +
      ENNReal.ofReal 288 * ENNReal.ofReal (∑ i : Fin 3, ‖H1.derivative (unitOpenCube 3) i v‖ ^ 2) := by
  let e := ∑ i : Fin 3, ‖H1.derivative (unitOpenCube 3) i v‖ ^ 2
  have he : 0 ≤ e := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hi (i : Fin 3) : ‖H1.derivative (unitOpenCube 3) i v‖ ≤ Real.sqrt e := by
    have hs := Finset.single_le_sum (f := fun j : Fin 3 => ‖H1.derivative (unitOpenCube 3) j v‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hh := Real.sq_sqrt he
    nlinarith [norm_nonneg (H1.derivative (unitOpenCube 3) i v), Real.sqrt_nonneg e]
  have hb : lpNorm (H1.value (unitOpenCube 3) v) 6 (volume.restrict (unitOpenCube 3)) ≤
      1 * R + 12 * Real.sqrt e := by
    have hh := v.unitOpenCube_sub_const_sobolev_six 0
    simp only [sub_zero, Fin.sum_univ_three] at hh
    linarith [hi 0, hi 1, hi 2]
  have hf := v.unitOpenCube_memLp_six
  have hh := lintegral_ofReal_six_rpow_le_of_lpNorm_bound hf.norm
    (Filter.Eventually.of_forall fun x => norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 12) hR he
    (by simpa only [lpNorm_norm hf.aestronglyMeasurable] using hb)
  norm_num only [one_pow, mul_one, show (2 : ℝ) * 12 ^ 2 = 288 by norm_num,
    ← ENNReal.ofReal_pow hR, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at hh
  exact hh

theorem lintegral_cube_six_squared_le_of_H1_family
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {ρ : α × Space 3 → ℝ} (v : α → H1 (unitOpenCube 3)) {R E : ℝ}
    (hR : 0 ≤ R) (hE : 0 ≤ E)
    (hrep : ∀ᵐ t ∂μ, H1.value (unitOpenCube 3) (v t) =ᵐ[volume.restrict (unitOpenCube 3)]
      fun x => ρ (t, x))
    (hL2 : ∀ᵐ t ∂μ, lpNorm (fun x => ρ (t, x)) 2 (volume.restrict (unitOpenCube 3)) ≤ R)
    (henergy : (∫⁻ t, ENNReal.ofReal (∑ i : Fin 3, ‖H1.derivative (unitOpenCube 3) i (v t)‖ ^ 2) ∂μ)
      ≤ ENNReal.ofReal E) :
    (∫⁻ t, (∫⁻ x in unitOpenCube 3, ENNReal.ofReal |ρ (t, x)| ^ (6 : ℝ)) ^ (1 / 3 : ℝ) ∂μ) ≤
      ENNReal.ofReal ((2 * R ^ 2 * (μ Set.univ).toReal + 288) * (1 + E)) := by
  have hs : ∀ᵐ t ∂μ,
      (∫⁻ x in unitOpenCube 3, ENNReal.ofReal |ρ (t, x)| ^ (6 : ℝ)) ^ (1 / 3 : ℝ) ≤
        ENNReal.ofReal (2 * R ^ 2) + ENNReal.ofReal 288 *
          ENNReal.ofReal (∑ i : Fin 3, ‖H1.derivative (unitOpenCube 3) i (v t)‖ ^ 2) := by
    filter_upwards [hrep, hL2] with t ht hlt
    have heq : lpNorm (H1.value (unitOpenCube 3) (v t)) 2 (volume.restrict (unitOpenCube 3)) =
        lpNorm (fun x => ρ (t, x)) 2 (volume.restrict (unitOpenCube 3)) := by
      have hf := Lp.memLp (H1.value (unitOpenCube 3) (v t))
      have hh := congrArg ENNReal.toReal (eLpNorm_congr_ae (p := 2) ht)
      simpa only [toReal_eLpNorm hf.aestronglyMeasurable,
        toReal_eLpNorm (hf.ae_eq ht).aestronglyMeasurable] using hh
    have hh := (v t).unitOpenCube_six_squared_le hR (heq.trans_le hlt)
    convert hh using 1
    congr 1
    exact lintegral_congr_ae (ht.mono fun x hx => by rw [hx]) |>.symm
  apply (lintegral_mono_ae hs).trans
  rw [lintegral_add_left measurable_const, lintegral_const,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ENNReal.ofReal (2 * R ^ 2) * μ Set.univ + ENNReal.ofReal 288 * ENNReal.ofReal E := by
      gcongr
    _ = ENNReal.ofReal (2 * R ^ 2 * (μ Set.univ).toReal + 288 * E) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (show 0 ≤ 2 * R ^ 2 by positivity),
        ENNReal.ofReal_mul (show (0 : ℝ) ≤ 288 by norm_num),
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg (sq_nonneg R) (ENNReal.toReal_nonneg (a := μ Set.univ))])

end PDE
