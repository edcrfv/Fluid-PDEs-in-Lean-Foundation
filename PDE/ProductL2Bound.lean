import PDE.WeightedEnergyReal
import PDE.MeanPoincare
import Mathlib.MeasureTheory.Integral.Prod

/-! An a.e. uniform spatial L² bound gives genuine product square integrability.
No sign condition or prescribed exceptional-time representative is required. -/

open MeasureTheory
open scoped ENNReal

namespace PDE

theorem integrable_sq_of_ae_uniform_L2
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [SFinite ν]
    {f : α × β → ℝ} {R : ℝ} (hf : Measurable f) (hR : 0 ≤ R)
    (hL2 : ∀ᵐ t ∂μ, MemLp (fun x => f (t, x)) 2 ν)
    (hb : ∀ᵐ t ∂μ, lpNorm (fun x => f (t, x)) 2 ν ≤ R) :
    Integrable (fun z => f z ^ 2) (μ.prod ν) ∧
      (∫⁻ z, ENNReal.ofReal (f z ^ 2) ∂μ.prod ν) ≤ ENNReal.ofReal (R ^ 2) * μ Set.univ := by
  have hbound : (∫⁻ z, ENNReal.ofReal (f z ^ 2) ∂μ.prod ν) ≤
      ENNReal.ofReal (R ^ 2) * μ Set.univ := by
    rw [lintegral_prod _ (hf.pow_const 2).ennreal_ofReal.aemeasurable]
    calc
      _ ≤ ∫⁻ _t, ENNReal.ofReal (R ^ 2) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hL2, hb] with t ht hbt
        rw [← ofReal_integral_eq_lintegral_ofReal ht.integrable_sq
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        rw [lpNorm_two_eq_sqrt_integral_sq ht] at hbt
        have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) hR).mpr hbt
        rwa [Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)] at hsq
      _ = _ := by rw [lintegral_const]
  refine ⟨?_, hbound⟩
  exact (lintegral_ofReal_ne_top_iff_integrable (hf.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp
      (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hbound)

end PDE
