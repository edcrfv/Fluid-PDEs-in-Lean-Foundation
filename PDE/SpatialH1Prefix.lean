import PDE.SpatialH1Family

/-! Prefix energies of a single sliced H¹ family. Uniqueness of distributional
derivatives identifies independently obtained prefix gradients with restrictions
of the global ones, so prefix-dependent subsequences cause no ambiguity. -/

open MeasureTheory Set InnerProductSpace
open scoped ENNReal

namespace PDE

theorem ofReal_sum_L2norm_sq_eq_lintegral
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    (g : ι → Lp ℝ 2 μ) :
    ENNReal.ofReal (∑ i, ‖g i‖ ^ 2) = ∫⁻ x, ENNReal.ofReal (∑ i, g i x ^ 2) ∂μ := by
  have he : (∫ x, ∑ i, g i x ^ 2 ∂μ) = ∑ i, ‖g i‖ ^ 2 := by
    rw [integral_finsetSum _ (fun i _ => (Lp.memLp (g i)).integrable_sq)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp [pow_two]
  rw [← he]
  exact ofReal_integral_eq_lintegral_ofReal
    (integrable_finsetSum _ (fun i _ => (Lp.memLp (g i)).integrable_sq))
    (Filter.Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- One H¹ family has the correct energy for every prefix and every separately
constructed prefix weak gradient of the same value field. -/
theorem exists_H1_family_with_prefix_energy
    {n : ℕ} {a T : ℝ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    [IsFiniteMeasure (volume.restrict Ω)]
    {u : Space (n + 1) → ℝ} {du : Fin n → Space (n + 1) → ℝ}
    (hu : MemLp u 2 (volume.restrict (intervalCylinder a T Ω)))
    (hd : ∀ i, MemLp (du i) 2 (volume.restrict (intervalCylinder a T Ω)))
    (hw : ∀ i, HasWeakPartialOn (intervalCylinder a T Ω) i.succ u (du i)) :
    ∃ v : ℝ → H1 Ω,
      (∀ᵐ t ∂volume.restrict (Ico a T),
        H1.value Ω (v t) =ᵐ[volume.restrict Ω] fun x => u (Fin.cons t x)) ∧
      AEMeasurable (fun t => ENNReal.ofReal (∑ i, ‖H1.derivative Ω i (v t)‖ ^ 2))
        (volume.restrict (Ico a T)) ∧
      ∀ t ≤ T, ∀ g : Fin n → DomainL2 (intervalCylinder a t Ω),
        (∀ i, HasWeakPartialOn (intervalCylinder a t Ω) i.succ u (g i)) →
        (∫⁻ r in Ico a t, ENNReal.ofReal (∑ i, ‖H1.derivative Ω i (v r)‖ ^ 2)) =
          ENNReal.ofReal (∑ i, ‖g i‖ ^ 2) := by
  obtain ⟨v, hv, _, hm, he⟩ := exists_H1_family_of_cylinder_weak_partials hΩ hu hd hw
  have htime : volume.restrict (Ico a T) = volume.restrict (Icc a T) :=
    Measure.restrict_congr_set Ico_ae_eq_Icc
  refine ⟨v, by simpa only [htime] using hv, by simpa only [htime] using hm, ?_⟩
  intro t ht g hg
  have hsub : intervalCylinder a t Ω ⊆ intervalCylinder a T Ω :=
    fun x hx => ⟨⟨hx.1.1, hx.1.2.trans_le ht⟩, hx.2⟩
  have hsame : ∀ i, du i =ᵐ[volume.restrict (intervalCylinder a t Ω)] g i :=
    fun i => ((hw i).mono hsub).unique (isOpen_intervalCylinder a t hΩ) (hg i)
  have hrestrict : (volume.restrict (Icc a T)).restrict (Ico a t) =
      volume.restrict (Ico a t) := by
    rw [Measure.restrict_restrict measurableSet_Ico,
      inter_eq_left.mpr (show Ico a t ⊆ Icc a T from fun _ hx => ⟨hx.1, hx.2.le.trans ht⟩)]
  have hprefix := he (Ico a t)
  rw [hrestrict] at hprefix
  rw [hprefix, Measure.restrict_congr_set (Ico_ae_eq_Icc (a := a) (b := t))]
  rw [(cylinderLift_measurePreserving a t hΩ.measurableSet).lintegral_comp_emb
    (Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)).toHomeomorph.measurableEmbedding
    (fun x => ENNReal.ofReal (∑ i, du i x ^ 2))]
  rw [ofReal_sum_L2norm_sq_eq_lintegral]
  apply lintegral_congr_ae
  filter_upwards [ae_all_iff.mpr hsame] with x hx
  simp only [hx]

end PDE
