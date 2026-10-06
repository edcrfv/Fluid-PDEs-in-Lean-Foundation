import PDE.WeightedEnergy
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Instances.Rat

/-! Extracting a full-time energy bound from cumulative inequalities valid only
at almost every time. No value or trace of the entropy at the terminal time is
assumed. Rational intervals and continuity from below recover total dissipation. -/

open MeasureTheory Set
open scoped ENNReal

namespace PDE

/-- A uniform a.e. bound on cumulative nonnegative integrals controls the integral
over the whole half-open time interval. This also detects divergence at T. -/
theorem lintegral_Ico_le_of_ae_cumulative_le {T : ℝ} (hT : 0 < T)
    (d : ℝ → ℝ≥0∞) {P : ℝ≥0∞}
    (h : ∀ᵐ t ∂volume.restrict (Ico 0 T), (∫⁻ s in Ico 0 t, d s) ≤ P) :
    (∫⁻ s in Ico 0 T, d s) ≤ P := by
  let J := {q : ℚ // (q : ℝ) < T}
  let S : J → Set ℝ := fun q => Ico 0 (q.1 : ℝ)
  have hcover : (⋃ q : J, S q) = Ico 0 T := by
    ext x
    constructor
    · intro hx
      obtain ⟨q, hq⟩ := mem_iUnion.mp hx
      exact ⟨hq.1, hq.2.trans q.2⟩
    · intro hx
      obtain ⟨q, hxq, hqT⟩ := exists_rat_btwn hx.2
      exact mem_iUnion.mpr ⟨⟨q, hqT⟩, hx.1, hxq⟩
  have hdir : Directed (· ⊆ ·) S := by
    intro q r
    by_cases hqr : q.1 ≤ r.1
    · refine ⟨r, ?_, subset_rfl⟩
      exact Ico_subset_Ico_right (by exact_mod_cast hqr)
    · refine ⟨q, subset_rfl, ?_⟩
      exact Ico_subset_Ico_right (by exact_mod_cast (le_of_not_ge hqr))
  rw [← hcover, setLIntegral_iUnion_of_directed d hdir]
  apply iSup_le
  intro q
  have hmax : max 0 (q.1 : ℝ) < T := max_lt hT q.2
  have hsub : Ioo (max 0 (q.1 : ℝ)) T ⊆ Ico 0 T := by
    intro x hx
    exact ⟨(le_max_left _ _).trans hx.1.le, hx.2⟩
  have hvol : volume (Ioo (max 0 (q.1 : ℝ)) T) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hmax))
  obtain ⟨t, ht, hdt⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol
    (ae_restrict_of_ae_restrict_of_subset hsub h)
  apply le_trans _ hdt
  exact lintegral_mono_set (Ico_subset_Ico_right ((le_max_right _ _).trans ht.1.le))

/-- A cumulative budget with a retained nonnegative error. The error contributes
to both the entropy supremum and total dissipation; it cannot be dropped. -/
theorem weightedEnergy_le_of_ae_cumulative_budget_with_error
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {T : ℝ} (hT : 0 < T) (ρ f : ℝ × α → ℝ≥0∞) (d P : ℝ → ℝ≥0∞)
    {κ J : ℝ≥0∞} (hκ0 : κ ≠ 0) (hκtop : κ ≠ ∞)
    (hbudget : ∀ᵐ t ∂volume.restrict (Ico 0 T),
      (∫⁻ x, ρ (t, x) * f (t, x) ∂ν) + κ * (∫⁻ s in Ico 0 t, d s) ≤
        (∫⁻ s in Ico 0 t, P s) + J) :
    weightedEnergy (volume.restrict (Ico 0 T)) ν ρ f d ≤
      (1 + κ⁻¹) * ((∫⁻ s in Ico 0 T, P s) + J) := by
  have hfull : ∀ᵐ t ∂volume.restrict (Ico 0 T),
      (∫⁻ x, ρ (t, x) * f (t, x) ∂ν) + κ * (∫⁻ s in Ico 0 t, d s) ≤
        (∫⁻ s in Ico 0 T, P s) + J := by
    filter_upwards [hbudget, ae_restrict_mem measurableSet_Ico] with t ht hmem
    exact ht.trans (add_le_add (lintegral_mono_set (Ico_subset_Ico_right hmem.2.le)) le_rfl)
  have hcum : ∀ᵐ t ∂volume.restrict (Ico 0 T),
      (∫⁻ s in Ico 0 t, κ * d s) ≤ (∫⁻ s in Ico 0 T, P s) + J := by
    filter_upwards [hfull] with t ht
    rw [lintegral_const_mul' κ d hκtop]
    exact (le_add_left le_rfl).trans ht
  have hD := lintegral_Ico_le_of_ae_cumulative_le hT (fun s => κ * d s) hcum
  rw [lintegral_const_mul' κ d hκtop] at hD
  have hD' : (∫⁻ s in Ico 0 T, d s) ≤ κ⁻¹ * ((∫⁻ s in Ico 0 T, P s) + J) := by
    have h := mul_le_mul_right hD κ⁻¹
    rwa [ENNReal.inv_mul_cancel_left hκ0 hκtop] at h
  calc
    _ ≤ ((∫⁻ s in Ico 0 T, P s) + J) + κ⁻¹ * ((∫⁻ s in Ico 0 T, P s) + J) :=
      weightedEnergy_le_of_bounds (hfull.mono fun _ ht => (le_add_right le_rfl).trans ht) hD'
    _ = _ := by ring

/-- A cumulative entropy/heat budget gives the energy's true supremum-plus-total
bound, with coefficient `1 + κ⁻¹`. Valid for a.e. time, including vacuum, and
without assuming a temperature value or budget at the terminal time. -/
theorem weightedEnergy_le_of_ae_cumulative_budget
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {T : ℝ} (hT : 0 < T) (ρ f : ℝ × α → ℝ≥0∞) (d P : ℝ → ℝ≥0∞)
    {κ : ℝ≥0∞} (hκ0 : κ ≠ 0) (hκtop : κ ≠ ∞)
    (hbudget : ∀ᵐ t ∂volume.restrict (Ico 0 T),
      (∫⁻ x, ρ (t, x) * f (t, x) ∂ν) + κ * (∫⁻ s in Ico 0 t, d s) ≤
        ∫⁻ s in Ico 0 t, P s) :
    weightedEnergy (volume.restrict (Ico 0 T)) ν ρ f d ≤
      (1 + κ⁻¹) * ∫⁻ s in Ico 0 T, P s := by
  simpa only [add_zero] using weightedEnergy_le_of_ae_cumulative_budget_with_error
    ν hT ρ f d P hκ0 hκtop (J := 0) (by simpa only [add_zero] using hbudget)

end PDE
