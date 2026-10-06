import PDE.CylinderSpatialSlicing
import PDE.SobolevTruncation

/-! One actual H¹ family from spatial weak slices, with measurable scalar
gradient energy and its physical integral on every restricted time set. No
pointwise representative or Bochner measurability of the H¹ map is asserted. -/

open MeasureTheory Set
open scoped ENNReal

namespace PDE

/-- Construct one family from joint L² fields and actual spatial weak partials.
Every restriction uses the same family; no uncountable intersection of null sets
is used to obtain the simultaneous integral identities. -/
theorem exists_H1_family_of_spatial_weak_partials
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {n : ℕ} {Ω : Set (Space n)} [IsFiniteMeasure (volume.restrict Ω)]
    {u : α × Space n → ℝ} {du : Fin n → α × Space n → ℝ}
    (hu : MemLp u 2 (μ.prod (volume.restrict Ω)))
    (hd : ∀ i, MemLp (du i) 2 (μ.prod (volume.restrict Ω)))
    (hw : ∀ᵐ t ∂μ, ∀ i, HasWeakPartialOn Ω i (fun x => u (t, x)) (fun x => du i (t, x))) :
    ∃ v : α → H1 Ω,
      (∀ᵐ t ∂μ, H1.value Ω (v t) =ᵐ[volume.restrict Ω] fun x => u (t, x)) ∧
      (∀ᵐ t ∂μ, ∀ i, H1.derivative Ω i (v t) =ᵐ[volume.restrict Ω] fun x => du i (t, x)) ∧
      AEMeasurable (fun t => ENNReal.ofReal (∑ i, ‖H1.derivative Ω i (v t)‖ ^ 2)) μ ∧
      ∀ A : Set α,
        (∫⁻ t in A, ENNReal.ofReal (∑ i, ‖H1.derivative Ω i (v t)‖ ^ 2) ∂μ) =
          ∫⁻ z, ENNReal.ofReal (∑ i, du i z ^ 2) ∂(μ.restrict A).prod (volume.restrict Ω) := by
  classical
  let P (t : α) (v : H1 Ω) : Prop :=
    (H1.value Ω v =ᵐ[volume.restrict Ω] fun x => u (t, x)) ∧
    ∀ i, H1.derivative Ω i v =ᵐ[volume.restrict Ω] fun x => du i (t, x)
  have hex : ∀ᵐ t ∂μ, ∃ v, P t v := by
    filter_upwards [memLp_two_slice_right_ae hu,
      ae_all_iff.mpr (fun i => memLp_two_slice_right_ae (hd i)), hw] with t ht hdt hwt
    exact ⟨H1.ofFunction _ _ ht hdt hwt, H1.value_ofFunction_ae _ _ ht hdt hwt,
      H1.derivative_ofFunction_ae _ _ ht hdt hwt⟩
  let v (t : α) : H1 Ω := if h : ∃ v, P t v then h.choose else 0
  have hv : ∀ᵐ t ∂μ, P t (v t) := hex.mono fun t ht => by
    simpa only [v, dite_eq_left ht] using ht.choose_spec
  have hmeas : AEMeasurable (fun z => ENNReal.ofReal (∑ i, du i z ^ 2))
      (μ.prod (volume.restrict Ω)) := by
    simpa only [Finset.sum_apply] using
      (Finset.aemeasurable_sum Finset.univ fun i _ =>
        (hd i).aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  have he : (fun t => ENNReal.ofReal (∑ i, ‖H1.derivative Ω i (v t)‖ ^ 2)) =ᵐ[μ]
      (fun t => ∫⁻ x in Ω, ENNReal.ofReal (∑ i, du i (t, x) ^ 2)) := by
    filter_upwards [hv] with t ht
    rw [H1.ofReal_gradientEnergy_eq_lintegral]
    apply lintegral_congr_ae
    filter_upwards [ae_all_iff.mpr ht.2] with x hx
    simp only [hx]
  refine ⟨v, hv.mono (fun _ ht => ht.1), hv.mono (fun _ ht => ht.2),
    hmeas.lintegral_prod_right'.congr he.symm, ?_⟩
  intro A
  rw [lintegral_prod _ (hmeas.mono_measure
    (Measure.prod_mono Measure.restrict_le_self le_rfl))]
  exact lintegral_congr_ae (he.filter_mono (ae_mono Measure.restrict_le_self))

/-- The vector-coordinate weak limit supplies one product-coordinate spatial
H¹ family and all of its restricted-time energy identities. -/
theorem exists_H1_family_of_cylinder_weak_partials
    {n : ℕ} {a b : ℝ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    [IsFiniteMeasure (volume.restrict Ω)]
    {u : Space (n + 1) → ℝ} {du : Fin n → Space (n + 1) → ℝ}
    (hu : MemLp u 2 (volume.restrict (intervalCylinder a b Ω)))
    (hd : ∀ i, MemLp (du i) 2 (volume.restrict (intervalCylinder a b Ω)))
    (hw : ∀ i, HasWeakPartialOn (intervalCylinder a b Ω) i.succ u (du i)) :
    ∃ v : ℝ → H1 Ω,
      (∀ᵐ t ∂volume.restrict (Icc a b),
        H1.value Ω (v t) =ᵐ[volume.restrict Ω] fun x => u (Fin.cons t x)) ∧
      (∀ᵐ t ∂volume.restrict (Icc a b), ∀ i,
        H1.derivative Ω i (v t) =ᵐ[volume.restrict Ω] fun x => du i (Fin.cons t x)) ∧
      AEMeasurable (fun t => ENNReal.ofReal (∑ i, ‖H1.derivative Ω i (v t)‖ ^ 2))
        (volume.restrict (Icc a b)) ∧
      ∀ A : Set ℝ,
        (∫⁻ t in A, ENNReal.ofReal (∑ i, ‖H1.derivative Ω i (v t)‖ ^ 2)
          ∂volume.restrict (Icc a b)) =
        ∫⁻ z, ENNReal.ofReal (∑ i, du i (Fin.cons z.1 z.2) ^ 2)
          ∂((volume.restrict (Icc a b)).restrict A).prod (volume.restrict Ω) := by
  have hμ := cylinderLift_measurePreserving a b hΩ.measurableSet
  exact exists_H1_family_of_spatial_weak_partials (hu.comp_measurePreserving hμ)
    (fun i => (hd i).comp_measurePreserving hμ) (ae_all_spatial_weak_partials hΩ hu hd hw)

end PDE
