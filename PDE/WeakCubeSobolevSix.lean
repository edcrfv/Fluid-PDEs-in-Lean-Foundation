import PDE.WeakCubeSobolev
import PDE.LpPower

/-! The power-and-Hölder step for cube H¹ Sobolev estimates.
L⁶ finiteness in the first lemma is removed by bounded approximation later. -/

open MeasureTheory Set
open scoped ENNReal

namespace PDE

/-- The L⁶ estimate for weak slices when the L⁶ norm is already finite.
This is the intermediate estimate applied to bounded smooth truncations. -/
theorem unitOpenCube_eLpNorm_six_le_of_memLp_of_weak_slices
    {f : Space 3 → ℝ} {df : Fin 3 → Space 3 → ℝ}
    (hf : Measurable f) (hd : ∀ i, Measurable (df i))
    (hf6 : MemLp f 6 (volume.restrict (unitOpenCube 3)))
    (hw : ∀ i : Fin 3, ∀ᵐ x ∂volume.restrict (unitOpenCube 3),
      HasWeakDerivativeOnInterval 0 1 (fun t => f (Function.update x i t))
        (fun t => df i (Function.update x i t))) :
    eLpNorm f 6 (volume.restrict (unitOpenCube 3)) ≤
      eLpNorm f 2 (volume.restrict (unitOpenCube 3)) +
        4 * ∑ i : Fin 3, eLpNorm (df i) 2 (volume.restrict (unitOpenCube 3)) := by
  let μ := volume.restrict (unitOpenCube 3)
  let N := eLpNorm f 6 μ
  have hp3 : eLpNorm (fun x => f x ^ 3) 2 μ = N ^ 3 := by
    rw [eLpNorm_real_pow μ f 2 (by norm_num : 0 < 3)]
    norm_num
    rfl
  have h4weak : ∀ i : Fin 3, ∀ᵐ x ∂μ,
      HasWeakDerivativeOnInterval 0 1 (fun t => f (Function.update x i t) ^ 4)
        (fun t => 4 * f (Function.update x i t) ^ 3 * df i (Function.update x i t)) := by
    intro i
    filter_upwards [hw i] with x hx
    have h := hx.comp_contDiff (by norm_num) (contDiff_id.pow 4)
    simpa using h
  have hm4 : Measurable (fun x : Space 3 => f x ^ 4) := hf.pow_const 4
  have hmd4 (i : Fin 3) : Measurable (fun x : Space 3 => 4 * f x ^ 3 * df i x) :=
    (measurable_const.mul (hf.pow_const 3)).mul (hd i)
  have hb := unitOpenCube_eLpNorm_three_halves_le_of_weak_slices
    (f := fun x => f x ^ 4) (df := fun i x => 4 * f x ^ 3 * df i x) hm4 hmd4 h4weak
  change eLpNorm (fun x => f x ^ 4) (3 / 2) μ ≤
    eLpNorm (fun x => f x ^ 4) 1 μ +
      ∑ i : Fin 3, eLpNorm (fun x => 4 * f x ^ 3 * df i x) 1 μ at hb
  have hp4 : eLpNorm (fun x => f x ^ 4) (3 / 2) μ = N ^ 4 := by
    rw [eLpNorm_real_pow μ f (3 / 2) (by norm_num : 0 < 4)]
    have he : (3 / 2 : ℝ≥0∞) * 4 = 6 := by
      calc
        _ = ((3 / 2 : ℝ≥0∞) * 2) * 2 := by ring
        _ = _ := by rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num)]; norm_num
    norm_num only [Nat.cast_ofNat]
    rw [he]
  rw [hp4] at hb
  have hm (v : Space 3 → ℝ) (hv : Measurable v) :
      eLpNorm (fun x => f x ^ 3 * v x) 1 μ ≤ N ^ 3 * eLpNorm v 2 μ := by
    have h := eLpNorm_smul_le_mul_eLpNorm (μ := μ) (p := 2) (q := 2) (r := 1)
      hv.aestronglyMeasurable (hf.pow_const 3).aestronglyMeasurable
    change eLpNorm (fun x => f x ^ 3 * v x) 1 μ ≤
      eLpNorm (fun x => f x ^ 3) 2 μ * eLpNorm v 2 μ at h
    rwa [hp3] at h
  have hf4 : eLpNorm (fun x => f x ^ 4) 1 μ ≤ N ^ 3 * eLpNorm f 2 μ := by
    simpa only [pow_succ] using hm f hf
  have hd4 (i : Fin 3) : eLpNorm (fun x => 4 * f x ^ 3 * df i x) 1 μ ≤
      4 * (N ^ 3 * eLpNorm (df i) 2 μ) := by
    calc
      _ = eLpNorm ((4 : ℝ) • (fun x => f x ^ 3 * df i x)) 1 μ := by
        congr 1
        funext x
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      _ = 4 * eLpNorm (fun x => f x ^ 3 * df i x) 1 μ := by
        rw [eLpNorm_const_smul]
        norm_num [← ofReal_norm]
      _ ≤ _ := mul_le_mul le_rfl (hm (df i) (hd i)) (by positivity) (by positivity)
  have hall : N ^ 4 ≤ N ^ 3 *
      (eLpNorm f 2 μ + 4 * ∑ i : Fin 3, eLpNorm (df i) 2 μ) := by
    calc
      _ ≤ _ := hb.trans (add_le_add hf4 (Finset.sum_le_sum fun i _ => hd4 i))
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  by_cases h0 : N = 0
  · change N ≤ _
    rw [h0]
    exact bot_le
  have hfin : N ^ 3 ≠ ∞ := ENNReal.pow_ne_top hf6.eLpNorm_lt_top.ne
  rw [show N ^ 4 = N ^ 3 * N by ring] at hall
  exact (ENNReal.mul_le_mul_iff_right (pow_ne_zero _ h0) hfin).mp hall

end PDE
