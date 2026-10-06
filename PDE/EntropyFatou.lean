import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Passing an entropy-plus-dissipation budget to a limit. Dissipation is kept
extended-valued, so finiteness is a consequence of the budget, not an assumption
hidden in a real integral. No domination of the dissipations is required. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace PDE

theorem entropy_add_lintegral_le_of_approximation
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {d : ℕ → α → ℝ≥0∞} {dlim : α → ℝ≥0∞}
    {F P : ℕ → ℝ≥0∞} {Flim Plim : ℝ≥0∞}
    (hd : ∀ n, AEMeasurable (d n) μ)
    (hdlim : ∀ᵐ x ∂μ, Tendsto (fun n => d n x) atTop (𝓝 (dlim x)))
    (hF : Tendsto F atTop (𝓝 Flim)) (hP : Tendsto P atTop (𝓝 Plim))
    (hbudget : ∀ n, F n + (∫⁻ x, d n x ∂μ) ≤ P n) :
    Flim + (∫⁻ x, dlim x ∂μ) ≤ Plim := by
  have hfatou : (∫⁻ x, dlim x ∂μ) ≤ liminf (fun n => ∫⁻ x, d n x ∂μ) atTop := by
    calc
      _ = ∫⁻ x, liminf (fun n => d n x) atTop ∂μ :=
        lintegral_congr_ae (hdlim.mono fun _ hx => hx.liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le' hd
  obtain ⟨g, hg, hgat⟩ := exists_seq_tendsto_liminf
    (u := fun n : ℕ => ∫⁻ x, d n x ∂μ) (f := atTop)
  have hle := le_of_tendsto_of_tendsto ((hF.comp hgat).add hg) (hP.comp hgat)
    (Filter.Eventually.of_forall fun n => hbudget (g n))
  exact (add_le_add le_rfl hfatou).trans hle

end PDE
