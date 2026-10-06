import PDE.WeakEntropyProduction
import PDE.CumulativeEnergy

/-! Extended-valued weak entropy production. Finiteness of production is a
consequence of the entropy inequality and an upper entropy bound, not an input.
The signed entropy action is kept nonnegative explicitly before using ofReal. -/

open MeasureTheory Set
open scoped ENNReal

namespace PDE

/-- The nonnegative extended production is tested without first converting it
to a real function. Singular additional positive production is permitted. -/
structure HasExtendedWeakEntropyProduction (T S₀ : ℝ) (S : ℝ → ℝ)
    (J : ℝ → ℝ≥0∞) : Prop where
  entropy_integrable : IntegrableOn S (Icc 0 T)
  test : ∀ φ, IsInitialTimeTest T φ →
    0 ≤ -φ 0 * S₀ - (∫ t in Icc 0 T, deriv φ t * S t) ∧
    (∫⁻ t in Icc 0 T, ENNReal.ofReal (φ t) * J t) ≤
      ENNReal.ofReal (-φ 0 * S₀ - (∫ t in Icc 0 T, deriv φ t * S t))

/-- A possibly singular production measure dominating J dt supplies the
extended weak inequality. Only compact-test integrability is assumed for the
measure; neither global finite mass nor integrability of J is required. -/
theorem HasExtendedWeakEntropyProduction.of_dominating_measure {T S₀ : ℝ}
    {S : ℝ → ℝ} {J : ℝ → ℝ≥0∞} {σ : Measure ℝ}
    (hS : IntegrableOn S (Icc 0 T)) (hJ : Measurable J)
    (hdom : (volume.restrict (Icc 0 T)).withDensity J ≤ σ)
    (htest : ∀ φ, IsInitialTimeTest T φ → Integrable φ σ ∧
      (∫ t, φ t ∂σ) ≤ -φ 0 * S₀ - (∫ t in Icc 0 T, deriv φ t * S t)) :
    HasExtendedWeakEntropyProduction T S₀ S J := by
  refine ⟨hS, fun φ hφ => ?_⟩
  obtain ⟨hi, hb⟩ := htest φ hφ
  refine ⟨(MeasureTheory.integral_nonneg hφ.nonneg).trans hb, ?_⟩
  calc
    _ = ∫⁻ t, ENNReal.ofReal (φ t) ∂(volume.restrict (Icc 0 T)).withDensity J := by
      rw [lintegral_withDensity_eq_lintegral_mul _ hJ hφ.smooth.continuous.measurable.ennreal_ofReal]
      simp only [Pi.mul_apply, mul_comm]
    _ ≤ ∫⁻ t, ENNReal.ofReal (φ t) ∂σ := lintegral_mono' hdom le_rfl
    _ = ENNReal.ofReal (∫ t, φ t ∂σ) :=
      (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hφ.nonneg)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hb

/-- Bounded truncations of production satisfy the ordinary real weak entropy
inequality. Their integrability follows from the truncation itself. -/
theorem HasExtendedWeakEntropyProduction.truncated {T S₀ : ℝ}
    {S : ℝ → ℝ} {J : ℝ → ℝ≥0∞}
    (h : HasExtendedWeakEntropyProduction T S₀ S J) (hJ : Measurable J) (n : ℕ) :
    HasWeakEntropyProduction T S₀ S (fun t => (min (J t) (n : ℝ≥0∞)).toReal) := by
  have hn (t : ℝ) : min (J t) (n : ℝ≥0∞) ≠ ∞ :=
    ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  have hi : IntegrableOn (fun t => (min (J t) (n : ℝ≥0∞)).toReal) (Icc 0 T) := by
    apply (integrable_const (n : ℝ)).mono' (hJ.min measurable_const).ennreal_toReal.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact_mod_cast ENNReal.toReal_mono (by simp : (n : ℝ≥0∞) ≠ ∞) (min_le_right (J t) _)
  refine ⟨h.entropy_integrable, hi, ?_⟩
  intro φ hφ
  have hpi : IntegrableOn (fun t => φ t * (min (J t) (n : ℝ≥0∞)).toReal) (Icc 0 T) := by
    simpa only [smul_eq_mul] using hi.continuousOn_smul hφ.smooth.continuous.continuousOn isCompact_Icc
  have he : ENNReal.ofReal (∫ t in Icc 0 T, φ t * (min (J t) (n : ℝ≥0∞)).toReal) =
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (φ t) * min (J t) (n : ℝ≥0∞) := by
    rw [ofReal_integral_eq_lintegral_ofReal hpi
      (Filter.Eventually.of_forall fun t => mul_nonneg (hφ.nonneg t) ENNReal.toReal_nonneg)]
    apply lintegral_congr
    intro t
    rw [ENNReal.ofReal_mul (hφ.nonneg t), ENNReal.ofReal_toReal (hn t)]
  have hb : (∫⁻ t in Icc 0 T, ENNReal.ofReal (φ t) * min (J t) (n : ℝ≥0∞)) ≤
      ENNReal.ofReal (-φ 0 * S₀ - (∫ t in Icc 0 T, deriv φ t * S t)) := by
    apply le_trans (lintegral_mono (fun t => ?_)) (h.test φ hφ).2
    gcongr
    exact min_le_left _ _
  rw [← he] at hb
  have hh := (ENNReal.ofReal_le_ofReal_iff (h.test φ hφ).1).mp hb
  linarith

/-- Cumulative extended production from legal weak tests, allowing infinity
in the input. Countably many truncations share one full-measure time set. -/
theorem HasExtendedWeakEntropyProduction.cumulative_bound {T S₀ : ℝ}
    {S : ℝ → ℝ} {J : ℝ → ℝ≥0∞}
    (h : HasExtendedWeakEntropyProduction T S₀ S J) (hJ : Measurable J) (hT : 0 < T) :
    ∀ᵐ t ∂volume.restrict (Ico 0 T), S₀ ≤ S t ∧
      (∫⁻ s in Ico 0 t, J s) ≤ ENNReal.ofReal (S t - S₀) := by
  have hb := ae_all_iff.mpr (fun n => (h.truncated hJ n).cumulative_bound hT)
  rw [← Measure.restrict_congr_set (Ico_ae_eq_Icc (a := (0 : ℝ)) (b := T))] at hb
  filter_upwards [hb, ae_restrict_mem measurableSet_Ico] with t ht htT
  have hbound (n : ℕ) : (∫⁻ s in Ico 0 t, min (J s) (n : ℝ≥0∞)) ≤
      ENNReal.ofReal (S t - S₀) := by
    have hh := ht n
    rw [integral_Icc_eq_integral_Ico] at hh
    have hi := (h.truncated hJ n).production_integrable.mono_set
      (show Ico (0 : ℝ) t ⊆ Icc 0 T from fun _ hs => ⟨hs.1, hs.2.le.trans htT.2.le⟩)
    have he := ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
    simp only [ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by simp) (min_le_right _ (n : ℝ≥0∞)))] at he
    rw [← he]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨by simpa using ht 0, ?_⟩
  have he (s : ℝ) : (⨆ n : ℕ, min (J s) (n : ℝ≥0∞)) = J s := by
    simpa only [ENNReal.iSup_natCast, inf_top_eq] using (inf_iSup_eq (J s) (fun n : ℕ => (n : ℝ≥0∞))).symm
  calc
    _ = ∫⁻ s in Ico 0 t, ⨆ n : ℕ, min (J s) (n : ℝ≥0∞) := by simp_rw [he]
    _ = ⨆ n : ℕ, ∫⁻ s in Ico 0 t, min (J s) (n : ℝ≥0∞) :=
      lintegral_iSup (fun _ => hJ.min measurable_const)
        (fun _ _ hnm s => min_le_min_left _ (by exact_mod_cast hnm))
    _ ≤ _ := iSup_le hbound

/-- A common upper entropy bound supplies the whole-interval production
bound, a.e. finiteness and real integrability, including near the final time. -/
theorem HasExtendedWeakEntropyProduction.finite_production {T S₀ U : ℝ}
    {S : ℝ → ℝ} {J : ℝ → ℝ≥0∞}
    (h : HasExtendedWeakEntropyProduction T S₀ S J) (hJ : Measurable J) (hT : 0 < T)
    (hU : ∀ᵐ t ∂volume.restrict (Ico 0 T), S t ≤ U) :
    (∫⁻ t in Ico 0 T, J t) ≤ ENNReal.ofReal (U - S₀) ∧
    (∀ᵐ t ∂volume.restrict (Ico 0 T), J t ≠ ∞) ∧
    IntegrableOn (fun t => (J t).toReal) (Ico 0 T) := by
  have hb : (∫⁻ t in Ico 0 T, J t) ≤ ENNReal.ofReal (U - S₀) := by
    apply lintegral_Ico_le_of_ae_cumulative_le hT
    filter_upwards [h.cumulative_bound hJ hT, hU] with t ht hu
    exact ht.2.trans (ENNReal.ofReal_le_ofReal (sub_le_sub_right hu S₀))
  have hf := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  exact ⟨hb, (ae_lt_top hJ hf).mono fun _ ht => ht.ne,
    integrable_toReal_of_lintegral_ne_top hJ.aemeasurable hf⟩

/-- Once the upper entropy bound has proved finiteness, conversion to the
real-valued weak interface is legitimate and loses no infinite production. -/
theorem HasExtendedWeakEntropyProduction.to_real {T S₀ U : ℝ}
    {S : ℝ → ℝ} {J : ℝ → ℝ≥0∞}
    (h : HasExtendedWeakEntropyProduction T S₀ S J) (hJ : Measurable J) (hT : 0 < T)
    (hU : ∀ᵐ t ∂volume.restrict (Ico 0 T), S t ≤ U) :
    HasWeakEntropyProduction T S₀ S (fun t => (J t).toReal) := by
  obtain ⟨_, hf, hi⟩ := h.finite_production hJ hT hU
  rw [Measure.restrict_congr_set (Ico_ae_eq_Icc (a := (0 : ℝ)) (b := T))] at hf
  have hi' : IntegrableOn (fun t => (J t).toReal) (Icc 0 T) := by
    rwa [IntegrableOn, Measure.restrict_congr_set (Ico_ae_eq_Icc (a := (0 : ℝ)) (b := T))] at hi
  refine ⟨h.entropy_integrable, hi', fun φ hφ => ?_⟩
  have hpi : IntegrableOn (fun t => φ t * (J t).toReal) (Icc 0 T) := by
    simpa only [smul_eq_mul] using hi'.continuousOn_smul hφ.smooth.continuous.continuousOn isCompact_Icc
  have he : ENNReal.ofReal (∫ t in Icc 0 T, φ t * (J t).toReal) =
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (φ t) * J t := by
    rw [ofReal_integral_eq_lintegral_ofReal hpi
      (Filter.Eventually.of_forall fun t => mul_nonneg (hφ.nonneg t) ENNReal.toReal_nonneg)]
    apply lintegral_congr_ae
    filter_upwards [hf] with t ht
    rw [ENNReal.ofReal_mul (hφ.nonneg t), ENNReal.ofReal_toReal ht]
  have hb := (h.test φ hφ).2
  rw [← he] at hb
  have hh := (ENNReal.ofReal_le_ofReal_iff (h.test φ hφ).1).mp hb
  linarith

/-- Infinite production with constant entropy is rejected. In contrast,
converting infinity to a real value before testing would lose this information. -/
theorem not_hasExtendedWeakEntropyProduction_constant_top {T S₀ : ℝ} (hT : 0 < T) :
    ¬ HasExtendedWeakEntropyProduction T S₀ (fun _ => S₀) (fun _ => ∞) := by
  intro h
  have hb := (h.finite_production measurable_const hT
    (Filter.Eventually.of_forall fun _ => le_rfl)).1
  apply hT.not_ge
  simpa using hb

end PDE
