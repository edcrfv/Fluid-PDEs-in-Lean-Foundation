import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! A derivative vanishes almost everywhere on each of its function's level sets.
The level set need not have measure zero. Points isolated to the right form a
countable exceptional set; elsewhere the derivative is determined by its values
on that level set. -/

open MeasureTheory Set Filter
open scoped Topology

namespace PDE

/-- This uses the actual derivative where it exists; the total derivative is
zero at non-differentiability points. No regularity or null-level-set premise is
required for this statement. -/
theorem ae_deriv_eq_zero_on_level (f : ℝ → ℝ) (c : ℝ) :
    ∀ᵐ x ∂volume, f x = c → deriv f x = 0 := by
  let s := {x | f x = c}
  let N := {x ∈ s | 𝓝[s ∩ Ioi x] x = ⊥}
  have hN : N.Countable := countable_setOfPred_isolated_right_within
  have ha : ∀ᵐ x ∂volume, x ∉ N := by
    simpa only [ae_iff, not_not, ofPred_mem_eq] using hN.measure_zero volume
  filter_upwards [ha] with x hx
  intro hfx
  by_cases hd : DifferentiableAt ℝ f x
  · have hne : 𝓝[s ∩ Ioi x] x ≠ ⊥ := fun h => hx ⟨hfx, h⟩
    have hu : UniqueDiffWithinAt ℝ (s ∩ Ioi x) x := by
      rw [uniqueDiffWithinAt_iff_accPt, accPt_principal_iff_nhdsWithin]
      have he : (s ∩ Ioi x) \ {x} = s ∩ Ioi x := by simp
      rw [he]
      exact neBot_iff.mpr hne
    have hz : HasDerivWithinAt f 0 (s ∩ Ioi x) x :=
      (hasDerivWithinAt_const x (s ∩ Ioi x) c).congr (fun _ hy => hy.1) hfx
    exact UniqueDiffWithinAt.eq_deriv _ hu hd.hasDerivAt.hasDerivWithinAt hz
  · exact deriv_zero_of_not_differentiableAt hd

end PDE
