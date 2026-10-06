import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Prod

/-! Strong L¹ convergence on a product yields strong L¹ convergence of slices
along one subsequence at almost every parameter. This is not a trace assertion
at a prescribed endpoint. -/

open Filter MeasureTheory
open scoped Topology ENNReal

namespace PDE

/-- Extract one subsequence for all almost-everywhere slices of a product L¹
limit. The slice integral is the actual L¹ error, not a signed integral. -/
theorem exists_subsequence_L1_slices
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : ℕ → α × β → ℝ} {g : α × β → ℝ}
    (hf : ∀ j, Integrable (f j) (μ.prod ν)) (hg : Integrable g (μ.prod ν))
    (hlim : Tendsto (fun j => ∫ z, ‖f j z - g z‖ ∂μ.prod ν) atTop (𝓝 0)) :
    ∃ q : ℕ → ℕ, StrictMono q ∧ ∀ᵐ t ∂μ,
      (∀ j, Integrable (fun x => f (q j) (t, x)) ν) ∧
      Integrable (fun x => g (t, x)) ν ∧
      Tendsto (fun j => ∫ x, ‖f (q j) (t, x) - g (t, x)‖ ∂ν) atTop (𝓝 0) := by
  let e (j : ℕ) (t : α) := ∫ x, ‖f j (t, x) - g (t, x)‖ ∂ν
  have hi (j : ℕ) : Integrable (e j) μ := ((hf j).sub hg).norm.integral_prod_left
  have hn (j : ℕ) (t : α) : 0 ≤ e j t := integral_nonneg fun _ => norm_nonneg _
  have he (j : ℕ) : eLpNorm (e j - (0 : α → ℝ)) 1 μ =
      ENNReal.ofReal (∫ z, ‖f j z - g z‖ ∂μ.prod ν) := by
    simp only [sub_zero, eLpNorm_one_eq_lintegral_enorm]
    simp_rw [Real.enorm_eq_ofReal (hn j _)]
    rw [← ofReal_integral_eq_lintegral_ofReal (hi j)
      (Eventually.of_forall (hn j))]
    exact congrArg ENNReal.ofReal (integral_prod _ ((hf j).sub hg).norm).symm
  have hm : TendstoInMeasure μ e atTop (0 : α → ℝ) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
      (fun j => (hi j).aestronglyMeasurable) aestronglyMeasurable_zero
    simp_rw [he]
    simpa using ENNReal.tendsto_ofReal hlim
  obtain ⟨q, hq, hqe⟩ := hm.exists_seq_tendsto_ae
  refine ⟨q, hq, ?_⟩
  filter_upwards [hqe, hg.prod_right_ae,
    ae_all_iff.mpr (fun j => (hf (q j)).prod_right_ae)] with t ht hgt hft
  exact ⟨hft, hgt, ht⟩

end PDE
