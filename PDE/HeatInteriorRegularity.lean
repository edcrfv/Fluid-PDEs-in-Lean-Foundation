import PDE.HeatLocalRegularity
import Mathlib.Topology.Compactness.Lindelof

/-!
# Interior smoothness of distributional heat solutions

Smooth local representatives agree on overlaps by continuous a.e. uniqueness.
A countable subcover preserves almost-everywhere equality when they are glued.
The resulting representative is jointly smooth on the open domain, satisfies
the heat equation pointwise, and is unique there. The cylinder corollary is the
English/Lean theorem documented in `docs/HEAT_INTERIOR_REGULARITY.md`.
-/

open MeasureTheory Filter Set
open scoped Topology ContDiff

namespace PDE

private theorem glue_smooth_local_representatives {n : ℕ}
    {Q : Set (Space (n + 1))} {u : Space (n + 1) → ℝ}
    (hloc : ∀ z ∈ Q, ∃ (U : Set (Space (n + 1))) (f : Space (n + 1) → ℝ),
      IsOpen U ∧ z ∈ U ∧ U ⊆ Q ∧ ContDiff ℝ ∞ f ∧ u =ᵐ[volume.restrict U] f) :
    ∃ v : Space (n + 1) → ℝ, ContDiffOn ℝ ∞ v Q ∧ u =ᵐ[volume.restrict Q] v := by
  classical
  choose U f hU hzU hUQ hf huf using (fun z : Q => hloc z.val z.property)
  have hcompat (a b : Q) : EqOn (f a) (f b) (U a ∩ U b) :=
    heat_continuousRepresentative_unique ((hU a).inter (hU b))
      (hf a).continuous.continuousOn (hf b).continuous.continuousOn
      (ae_restrict_of_ae_restrict_of_subset inter_subset_left (huf a))
      (ae_restrict_of_ae_restrict_of_subset inter_subset_right (huf b))
  let v : Space (n + 1) → ℝ := fun x => if hx : x ∈ Q then f ⟨x, hx⟩ x else 0
  have hvloc (a : Q) : EqOn v (f a) (U a) := by
    intro x hx
    simp only [v, dite_eq_left (hUQ a hx)]
    exact hcompat ⟨x, hUQ a hx⟩ a ⟨hzU _, hx⟩
  refine ⟨v, ?_, ?_⟩
  · intro x hx
    apply ContDiffAt.contDiffWithinAt
    apply (hf ⟨x, hx⟩).contDiffAt.congr_of_eventuallyEq
    filter_upwards [(hU ⟨x, hx⟩).mem_nhds (hzU ⟨x, hx⟩)] with y hy
    exact hvloc ⟨x, hx⟩ hy
  · have hcover : Q ⊆ ⋃ a : Q, U a := by
      intro x hx
      exact mem_iUnion_of_mem ⟨x, hx⟩ (hzU ⟨x, hx⟩)
    obtain ⟨s, hs, hscover⟩ := (HereditarilyLindelofSpace.isLindelof Q).elim_countable_subcover U hU hcover
    have hfull : u =ᵐ[volume.restrict (⋃ a ∈ s, U a)] v := by
      apply (ae_eq_restrict_biUnion_iff U hs u v).mpr
      intro a _
      apply (huf a).trans
      filter_upwards [ae_restrict_mem (hU a).measurableSet] with x hx
      exact (hvloc a hx).symm
    exact ae_restrict_of_ae_restrict_of_subset hscover hfull

/-- Interior hypoellipticity of the homogeneous heat equation on an arbitrary
open space–time domain: every locally integrable distributional solution has a
unique smooth representative, and that representative is classically caloric. -/
theorem IsDistributionalHeatSolution.exists_smooth_representative {n : ℕ}
    (hn : 0 < n) {Q : Set (Space (n + 1))} {u : Space (n + 1) → ℝ}
    (hu : IsDistributionalHeatSolution Q u) (hQ : IsOpen Q) :
    ∃ v : Space (n + 1) → ℝ,
      ContDiffOn ℝ ∞ v Q ∧ u =ᵐ[volume.restrict Q] v ∧
      (∀ z ∈ Q, coordDeriv 0 v z = spaceTimeLaplacian v z) ∧
      (∀ w : Space (n + 1) → ℝ, ContDiffOn ℝ ∞ w Q →
        u =ᵐ[volume.restrict Q] w → EqOn w v Q) := by
  obtain ⟨v, hv, huv⟩ := glue_smooth_local_representatives
    (fun z hz => hu.exists_smooth_local_representative hn hQ hz)
  refine ⟨v, hv, huv, (isDistributionalHeatSolution_iff_of_contDiffOn hQ hv).mp (hu.congr huv), ?_⟩
  intro w hw huw
  exact heat_continuousRepresentative_unique hQ hw.continuousOn hv.continuousOn huw huv

/-- Every weak heat solution on `(0,T) × Ω`, with Ω open, has a unique jointly
smooth representative in the interior. No boundary regularity is assumed. -/
theorem heat_interior_smooth {n : ℕ} (hn : 0 < n)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) {T : ℝ} (_hT : 0 < T)
    {u : Space (n + 1) → ℝ} (hu : IsDistributionalHeatSolution (heatCylinder Ω T) u) :
    ∃ v : Space (n + 1) → ℝ,
      ContDiffOn ℝ ∞ v (heatCylinder Ω T) ∧
      u =ᵐ[volume.restrict (heatCylinder Ω T)] v ∧
      (∀ z ∈ heatCylinder Ω T, coordDeriv 0 v z = spaceTimeLaplacian v z) ∧
      (∀ w : Space (n + 1) → ℝ, ContDiffOn ℝ ∞ w (heatCylinder Ω T) →
        u =ᵐ[volume.restrict (heatCylinder Ω T)] w → EqOn w v (heatCylinder Ω T)) :=
  hu.exists_smooth_representative hn (isOpen_heatCylinder hΩ T)

end PDE
