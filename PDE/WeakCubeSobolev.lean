import PDE.CubeGridBound
import PDE.CubeWeakSlices
import PDE.IntervalWeakBound

/-! Nonzero-boundary cube Sobolev estimates directly from weak line identities. -/

open MeasureTheory Set
open scoped ENNReal

namespace PDE

/-- The W¹,¹ cube Sobolev estimate from actual weak derivatives on a.e. line.
The extended-norm formulation also covers an infinite right-hand side. -/
theorem unitOpenCube_eLpNorm_three_halves_le_of_weak_slices
    {f : Space 3 → ℝ} {df : Fin 3 → Space 3 → ℝ}
    (hf : Measurable f) (hd : ∀ i, Measurable (df i))
    (hw : ∀ i : Fin 3, ∀ᵐ x ∂volume.restrict (unitOpenCube 3),
      HasWeakDerivativeOnInterval 0 1 (fun t => f (Function.update x i t))
        (fun t => df i (Function.update x i t))) :
    eLpNorm f (3 / 2) (volume.restrict (unitOpenCube 3)) ≤
      eLpNorm f 1 (volume.restrict (unitOpenCube 3)) +
        ∑ i : Fin 3, eLpNorm (df i) 1 (volume.restrict (unitOpenCube 3)) := by
  let g : Space 3 → ℝ≥0∞ := fun x => ‖f x‖ₑ + ∑ i : Fin 3, ‖df i x‖ₑ
  have hg : Measurable g := hf.enorm.add (Finset.measurable_sum _ fun i _ => (hd i).enorm)
  have hb : ∀ᵐ x ∂volume.restrict (unitOpenCube 3), ∀ i : Fin 3,
      ‖f x‖ₑ ≤ ∫⁻ t, g (Function.update x i t) ∂unitIntervalMeasure := by
    rw [ae_all_iff]
    intro i
    have hi : Measurable (fun x : Space 3 =>
        ∫⁻ t, g (Function.update x i t) ∂unitIntervalMeasure) := by
      apply Measurable.lintegral_prod_right
      exact hg.comp (by fun_prop)
    apply ae_unitOpenCube_of_ae_update i (measurableSet_le hf.enorm hi)
    filter_upwards [hw i] with x hx
    filter_upwards [hx.ae_enorm_le_lintegral_enorm] with t ht
    simp only [Function.update_idem]
    refine ht.trans ?_
    have hm : Measurable (fun s : ℝ => ‖f (Function.update x i s)‖ₑ) :=
      hf.enorm.comp (by fun_prop)
    rw [← lintegral_add_left hm]
    apply lintegral_mono
    intro s
    exact add_le_add le_rfl (Finset.single_le_sum
      (f := fun j : Fin 3 => ‖df j (Function.update x i s)‖ₑ) (fun j _ => bot_le)
      (Finset.mem_univ i))
  have h := unitOpenCube_eLpNorm_le_of_line_integrals hg hb
  simpa only [g, lintegral_add_left hf.enorm,
    lintegral_finsetSum _ (fun i _ => (hd i).enorm), eLpNorm_one_eq_lintegral_enorm] using h

end PDE
