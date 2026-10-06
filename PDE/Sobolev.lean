import PDE.WeakDerivative
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# First-order Sobolev membership

`MemW1p` is a membership predicate on representatives, not yet a complete normed space.
The intended Banach-space range is `1 ≤ p`; the predicate itself also makes sense for `p < 1`.
General orders, a.e. quotients, completeness, traces, and `W₀^{1,p}` remain to be developed.
-/

open MeasureTheory
open scoped ENNReal

namespace PDE

/-- `u` and all its first weak partial derivatives belong to `Lᵖ(ℝⁿ)`. -/
def MemW1p {n : ℕ} (p : ℝ≥0∞) (u : Space n → ℝ) : Prop :=
  MemLp u p volume ∧ LocallyIntegrable u volume ∧
    ∃ du : Fin n → Space n → ℝ,
      ∀ i, HasWeakPartial i u (du i) ∧ MemLp (du i) p volume

theorem MemW1p.zero {n : ℕ} (p : ℝ≥0∞) : MemW1p (n := n) p (fun _ => 0) := by
  exact ⟨MemLp.zero, locallyIntegrable_zero, fun _ _ => 0,
    fun i => ⟨HasWeakPartial.zero i, MemLp.zero⟩⟩

theorem MemW1p.add {n : ℕ} {p : ℝ≥0∞} {u v : Space n → ℝ}
    (hu : MemW1p p u) (hv : MemW1p p v) : MemW1p p (u + v) := by
  obtain ⟨huLp, huLoc, du, hdu⟩ := hu
  obtain ⟨hvLp, hvLoc, dv, hdv⟩ := hv
  exact ⟨huLp.add hvLp, huLoc.add hvLoc, fun i => du i + dv i,
    fun i => ⟨(hdu i).1.add (hdv i).1, (hdu i).2.add (hdv i).2⟩⟩

end PDE
