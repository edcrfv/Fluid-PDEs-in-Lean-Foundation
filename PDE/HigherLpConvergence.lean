import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Higher Lp bounds give uniform integrability at a strictly lower exponent.
Convergence in measure then yields strong convergence. No pointwise common
majorant or preassigned integrability of the limit is required. -/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace PDE

/-- The strict exponent gap makes concentration on small sets uniformly
small. The upper norm bound is an extended finite number. -/
theorem unifIntegrable_of_higher_eLpNorm_bound
    {α β ι : Type*} [MeasurableSpace α] [NormedAddCommGroup β] {μ : Measure α}
    {f : ι → α → β} {p q C : ℝ≥0∞}
    (hp : 0 < p) (hpq : p < q) (hq : q ≠ ∞) (hC : C ≠ ∞)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (hb : ∀ i, eLpNorm (f i) q μ ≤ C) :
    UnifIntegrable f p μ := by
  have hpt : p ≠ ∞ := (hpq.trans_le le_top).ne
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp.ne' hpt
  have hpqr : p.toReal < q.toReal := (ENNReal.toReal_lt_toReal hpt hq).mpr hpq
  have hexp : 0 < 1 / p.toReal - 1 / q.toReal :=
    sub_pos.mpr (one_div_lt_one_div_of_lt hpr hpqr)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hC hexp)
  · exact fun _ => bot_le
  · intro ε
    apply iSup_le
    intro i
    apply iSup_le
    intro s
    apply iSup_le
    intro hs
    have he := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq.le (hf i).restrict
      (μ := μ.restrict s)
    rw [Measure.restrict_apply_univ] at he
    apply he.trans
    exact mul_le_mul' ((eLpNorm_restrict_le _ _ _ _).trans (hb i))
      (ENNReal.rpow_le_rpow hs hexp.le)

/-- On a finite measure space, a bounded higher Lp norm and convergence in
measure imply membership and strong convergence at every intermediate exponent. -/
theorem memLp_and_tendsto_of_higher_bound_of_inMeasure
    {α β : Type*} [MeasurableSpace α] [NormedAddCommGroup β]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℕ → α → β} {g : α → β}
    {p q C : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p < q) (hq : q ≠ ∞) (hC : C ≠ ∞)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (hg : AEStronglyMeasurable g μ)
    (hb : ∀ i, eLpNorm (f i) q μ ≤ C) (hl : TendstoInMeasure μ f atTop g) :
    MemLp g p μ ∧ Tendsto (fun i => eLpNorm (f i - g) p μ) atTop (𝓝 0) := by
  have hgq : MemLp g q μ := ⟨hg,
    (eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall hb) hl hf).trans_lt (lt_top_iff_ne_top.mpr hC)⟩
  have hgp := hgq.mono_exponent hpq.le
  exact ⟨hgp, tendsto_Lp_finite_of_tendstoInMeasure hp (hpq.trans_le le_top).ne hf hgp
    (unifIntegrable_of_higher_eLpNorm_bound (zero_lt_one.trans_le hp) hpq hq hC hf hb) hl⟩

/-- Adding a vanishing spatial constant preserves strong L1 convergence on
a finite measure space. This handles an artificial storage parameter. -/
theorem tendsto_L1_add_vanishing_constant
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : ℕ → α → ℝ} {g : α → ℝ} {δ : ℕ → ℝ}
    (hf : ∀ j, Integrable (f j) μ) (hg : Integrable g μ)
    (hl : Tendsto (fun j => ∫ x, ‖f j x - g x‖ ∂μ) atTop (𝓝 0))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, ‖f j x + δ j - g x‖ ∂μ) atTop (𝓝 0) := by
  apply squeeze_zero (fun j => integral_nonneg fun x => norm_nonneg _) (g := fun j =>
    (∫ x, ‖f j x - g x‖ ∂μ) + μ.real univ * ‖δ j‖)
  · intro j
    have hh := integral_mono (((hf j).add (integrable_const (δ j))).sub hg).norm
      (((hf j).sub hg).norm.add (integrable_const ‖δ j‖))
      (fun x => by
        change ‖f j x + δ j - g x‖ ≤ ‖f j x - g x‖ + ‖δ j‖
        simpa only [add_sub_right_comm] using norm_add_le (f j x - g x) (δ j))
    simp only [Pi.add_apply] at hh
    rw [integral_add ((hf j).sub hg).norm (integrable_const ‖δ j‖)] at hh
    simpa only [Pi.add_apply, Pi.sub_apply, integral_const, smul_eq_mul] using hh
  · simpa using hl.add (hδ.norm.const_mul (μ.real univ))

end PDE
