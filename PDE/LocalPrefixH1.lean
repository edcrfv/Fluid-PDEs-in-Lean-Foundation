import PDE.SpatialH1Prefix
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Instances.Rat

/-! Assemble a single H¹ time family from weak spatial derivatives available
only on almost-everywhere prefixes. Uniqueness of the H¹ value class gives a
canonical choice on each time slice. Countable exhaustion supplies global
scalar-energy measurability, without assuming a full-cylinder L² gradient. -/

open MeasureTheory Set
open scoped ENNReal

namespace PDE

/-- A.e.-prefix weak derivatives suffice to construct one H¹ family, with the
correct energy for every strict prefix. Neither global gradient integrability
nor a trace or budget at the prescribed terminal time is assumed. -/
theorem exists_H1_family_of_ae_prefix_weak_partials
    {n : ℕ} {T : ℝ} (hT : 0 < T) {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    [IsFiniteMeasure (volume.restrict Ω)] {u : Space (n + 1) → ℝ}
    (hu : MemLp u 2 (volume.restrict (intervalCylinder 0 T Ω)))
    (hw : ∀ᵐ t ∂volume.restrict (Ico 0 T),
      ∃ g : Fin n → DomainL2 (intervalCylinder 0 t Ω),
        ∀ i, HasWeakPartialOn (intervalCylinder 0 t Ω) i.succ u (g i)) :
    ∃ v : ℝ → H1 Ω,
      (∀ᵐ t ∂volume.restrict (Ico 0 T),
        H1.value Ω (v t) =ᵐ[volume.restrict Ω] fun x => u (Fin.cons t x)) ∧
      AEMeasurable (fun t => ENNReal.ofReal (∑ i, ‖H1.derivative Ω i (v t)‖ ^ 2))
        (volume.restrict (Ico 0 T)) ∧
      ∀ t < T, ∀ g : Fin n → DomainL2 (intervalCylinder 0 t Ω),
        (∀ i, HasWeakPartialOn (intervalCylinder 0 t Ω) i.succ u (g i)) →
        (∫⁻ r in Ico 0 t, ENNReal.ofReal (∑ i, ‖H1.derivative Ω i (v r)‖ ^ 2)) =
          ENNReal.ofReal (∑ i, ‖g i‖ ^ 2) := by
  classical
  let P (t : ℝ) (w : H1 Ω) :=
    H1.value Ω w =ᵐ[volume.restrict Ω] fun x => u (Fin.cons t x)
  let v (t : ℝ) : H1 Ω := if h : ∃ w, P t w then h.choose else 0
  have hcanonical (t : ℝ) (w : H1 Ω) (ht : P t w) : v t = w := by
    have hx : ∃ w, P t w := ⟨w, ht⟩
    have hv : P t (v t) := by simpa only [v, dite_eq_left hx] using hx.choose_spec
    exact H1.value_injective hΩ (Lp.ext (hv.trans ht.symm))
  have hlocal (t : ℝ) (ht : t < T) :
      (∀ᵐ r ∂volume.restrict (Ico 0 t), P r (v r)) ∧
      AEMeasurable (fun r => ENNReal.ofReal (∑ i, ‖H1.derivative Ω i (v r)‖ ^ 2))
        (volume.restrict (Ico 0 t)) ∧
      ∀ g : Fin n → DomainL2 (intervalCylinder 0 t Ω),
        (∀ i, HasWeakPartialOn (intervalCylinder 0 t Ω) i.succ u (g i)) →
        (∫⁻ r in Ico 0 t, ENNReal.ofReal (∑ i, ‖H1.derivative Ω i (v r)‖ ^ 2)) =
          ENNReal.ofReal (∑ i, ‖g i‖ ^ 2) := by
    have hsub : Ioo (max 0 t) T ⊆ Ico 0 T :=
      fun _ hx => ⟨(le_max_left _ _).trans hx.1.le, hx.2⟩
    have hvol : volume (Ioo (max 0 t) T) ≠ 0 := by
      rw [Real.volume_Ioo]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr (max_lt hT ht)))
    obtain ⟨s, hs, d, hd⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol
      (ae_restrict_of_ae_restrict_of_subset hsub hw)
    have hts : t ≤ s := (le_max_right _ _).trans hs.1.le
    have hcs : intervalCylinder 0 s Ω ⊆ intervalCylinder 0 T Ω :=
      fun _ hx => ⟨⟨hx.1.1, hx.1.2.trans hs.2⟩, hx.2⟩
    obtain ⟨w, hwv, hwm, hwe⟩ := exists_H1_family_with_prefix_energy hΩ
      (hu.mono_measure (Measure.restrict_mono hcs le_rfl)) (fun i => Lp.memLp (d i)) hd
    have hsame : v =ᵐ[volume.restrict (Ico 0 t)] w :=
      (ae_restrict_of_ae_restrict_of_subset (Ico_subset_Ico_right hts) hwv).mono
        fun r hr => hcanonical r (w r) hr
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [hsame,
        ae_restrict_of_ae_restrict_of_subset (Ico_subset_Ico_right hts) hwv] with r hr hv
      exact hr ▸ hv
    · exact (hwm.mono_measure (Measure.restrict_mono (Ico_subset_Ico_right hts) le_rfl)).congr
        (hsame.mono fun _ hx => congrArg
          (fun z => ENNReal.ofReal (∑ i, ‖H1.derivative Ω i z‖ ^ 2)) hx.symm)
    · intro g hg
      rw [← hwe t hts g hg]
      exact lintegral_congr_ae (hsame.mono fun _ hx => congrArg
        (fun z => ENNReal.ofReal (∑ i, ‖H1.derivative Ω i z‖ ^ 2)) hx)
  let J := {q : ℚ // (q : ℝ) < T}
  let S : J → Set ℝ := fun q => Ico 0 (q.1 : ℝ)
  have hcover : (⋃ q, S q) = Ico 0 T := by
    ext x
    constructor
    · intro hx
      obtain ⟨q, hq⟩ := mem_iUnion.mp hx
      exact ⟨hq.1, hq.2.trans q.2⟩
    · intro hx
      obtain ⟨q, hxq, hqT⟩ := exists_rat_btwn hx.2
      exact mem_iUnion.mpr ⟨⟨q, hqT⟩, hx.1, hxq⟩
  refine ⟨v, ?_, ?_, fun t ht => (hlocal t ht).2.2⟩
  · rw [← hcover, ae_restrict_iUnion_iff]
    exact fun q => (hlocal q.1 q.2).1
  · rw [← hcover]
    exact AEMeasurable.iUnion fun q => (hlocal q.1 q.2).2.1

end PDE
