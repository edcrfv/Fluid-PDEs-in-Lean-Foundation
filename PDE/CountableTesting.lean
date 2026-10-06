import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-! A common full-measure set for continuous tests in a separable parameter space. -/

open MeasureTheory Set TopologicalSpace

namespace PDE

/-- A continuous family of test residuals can be made zero simultaneously on
one full-measure set. The test index itself need not be countable: only its
image in the ambient normed parameter space must be separable. -/
theorem ae_forall_continuous_tests {α ι V : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup V] [SeparableSpace V]
    (test : ι → V) (R : α → V → ℝ)
    (hc : ∀ᵐ x ∂μ, Continuous (R x))
    (hzero : ∀ i, ∀ᵐ x ∂μ, R x (test i) = 0) :
    ∀ᵐ x ∂μ, ∀ i, R x (test i) = 0 := by
  obtain ⟨s, hs, hsc, hsd⟩ :=
    (IsSeparable.of_separableSpace (Set.range test)).exists_countable_dense_subset
  have hz : ∀ᵐ x ∂μ, ∀ v ∈ s, R x v = 0 := by
    apply (ae_ball_iff hsc).mpr
    intro v hv
    obtain ⟨i, rfl⟩ := hs hv
    exact hzero i
  filter_upwards [hc, hz] with x hcx hx
  have hclosed : IsClosed {v | R x v = 0} := isClosed_eq hcx continuous_const
  have hcl : closure s ⊆ {v | R x v = 0} := closure_minimal hx hclosed
  exact fun i => hcl (hsd ⟨i, rfl⟩)

end PDE
