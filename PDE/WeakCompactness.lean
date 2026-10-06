import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual

open InnerProductSpace Filter Set
open scoped Topology

namespace PDE
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [TopologicalSpace.SeparableSpace V]

/-- Bounded sequences in a separable real Hilbert space have weakly convergent subsequences. -/
theorem exists_weakly_convergent_subsequence (u : ℕ → V) {C : ℝ} (hC : ∀ k, ‖u k‖ ≤ C) :
    ∃ v : V, ‖v‖ ≤ C ∧ ∃ r : ℕ → ℕ, StrictMono r ∧
      ∀ w : V, Tendsto (fun k => inner ℝ (u (r k)) w) atTop (𝓝 (inner ℝ v w)) := by
  let f : ℕ → WeakDual ℝ V := fun k => StrongDual.toWeakDual (toDual ℝ V (u k))
  have hf : ∀ k, f k ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ V) C := by
    intro k
    simpa [f, Metric.mem_closedBall, dist_zero_right] using hC k
  obtain ⟨g, hg, r, hr, hlim⟩ := (WeakDual.isSeqCompact_closedBall ℝ V 0 C) hf
  refine ⟨(toDual ℝ V).symm g.toStrongDual, ?_, r, hr, ?_⟩
  · simpa only [LinearIsometryEquiv.norm_map, mem_preimage, Metric.mem_closedBall,
      dist_zero_right] using hg
  · intro w
    have h := (WeakDual.eval_continuous w).continuousAt.tendsto.comp hlim
    simpa only [f, Function.comp_def, StrongDual.toWeakDual_apply, toDual_apply_apply,
      toDual_symm_apply, WeakDual.toStrongDual_apply] using h
end PDE
