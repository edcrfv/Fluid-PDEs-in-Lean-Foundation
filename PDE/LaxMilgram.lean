import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A variational interface to Mathlib's Lax–Milgram theorem

The existence theorem is reused from Mathlib; the local contribution is the PDE-facing
statement `∃! u, ∀ v, B u v = ℓ v` and its explicit coercivity estimate.
The concrete `H₀¹(Ω)` Poisson instantiation is in `PDE.EllipticWeakSolutions`.
-/

open InnerProductSpace

namespace PDE

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The abstract weak equation for a bounded bilinear form and continuous load. -/
def IsVariationalSolution (B : V →L[ℝ] V →L[ℝ] ℝ) (ℓ : V →L[ℝ] ℝ) (u : V) : Prop :=
  ∀ v, B u v = ℓ v

theorem exists_unique_variationalSolution (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (ℓ : V →L[ℝ] ℝ) : ∃! u, IsVariationalSolution B ℓ u := by
  let A := hB.continuousLinearEquivOfBilin
  let f := (toDual ℝ V).symm ℓ
  refine ⟨A.symm f, ?_, ?_⟩
  · intro v
    rw [← hB.continuousLinearEquivOfBilin_apply]
    change inner ℝ (A (A.symm f)) v = ℓ v
    rw [A.apply_symm_apply]
    exact toDual_symm_apply
  · intro u hu
    apply A.injective
    rw [A.apply_symm_apply]
    exact (hB.unique_continuousLinearEquivOfBilin
      (fun v => (toDual_symm_apply (𝕜 := ℝ)).trans (hu v).symm)).symm

omit [CompleteSpace V] in
/-- Testing against the solution gives the standard bound `‖u‖ ≤ ‖ℓ‖ / α`. -/
theorem IsVariationalSolution.norm_le {B : V →L[ℝ] V →L[ℝ] ℝ}
    {ℓ : V →L[ℝ] ℝ} {u : V} (hu : IsVariationalSolution B ℓ u)
    {α : ℝ} (hα : 0 < α) (hcoercive : ∀ v, α * ‖v‖ * ‖v‖ ≤ B v v) :
    ‖u‖ ≤ ‖ℓ‖ / α := by
  have hbound : α * ‖u‖ * ‖u‖ ≤ ‖ℓ‖ * ‖u‖ := by
    calc
      α * ‖u‖ * ‖u‖ ≤ B u u := hcoercive u
      _ = ℓ u := hu u
      _ ≤ ‖ℓ u‖ := le_abs_self _
      _ ≤ ‖ℓ‖ * ‖u‖ := ℓ.le_opNorm u
  by_cases hzero : ‖u‖ = 0
  · rw [hzero]
    positivity
  · have hpos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    apply (le_div_iff₀ hα).2
    nlinarith

end PDE
