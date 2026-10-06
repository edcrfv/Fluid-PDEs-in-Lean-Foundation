import PDE.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Abel

/-!
# Galerkin variational approximation

Existence and uniqueness hold on complete trial subspaces, hence in particular on finite-dimensional
ones. Galerkin orthogonality gives Céa's comparison with every trial approximation. Constructing a
parabolic Galerkin ODE and taking its limit remain separate tasks.
-/

namespace PDE

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem galerkin_orthogonality {B : V →L[ℝ] V →L[ℝ] ℝ} {ℓ : V →L[ℝ] ℝ}
    {u uh : V} (S : Submodule ℝ V) (hu : IsVariationalSolution B ℓ u)
    (huh : ∀ v ∈ S, B uh v = ℓ v) : ∀ v ∈ S, B (u - uh) v = 0 := by
  intro v hv
  rw [map_sub]
  change B u v - B uh v = 0
  rw [hu v, huh v hv, sub_self]

/-- Variational existence on any complete trial subspace, including every finite-dimensional one. -/
theorem exists_unique_galerkinSolution (S : Submodule ℝ V) [CompleteSpace S]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (ℓ : V →L[ℝ] ℝ) :
    ∃! uh : S, ∀ v : S, B (uh : V) (v : V) = ℓ (v : V) := by
  let BS : S →L[ℝ] S →L[ℝ] ℝ := B.bilinearComp S.subtypeL S.subtypeL
  have hBS : IsCoercive BS := by
    obtain ⟨α, hα, hcoercive⟩ := hB
    exact ⟨α, hα, fun v => hcoercive v⟩
  exact exists_unique_variationalSolution BS hBS (ℓ.comp S.subtypeL)

/-- Céa's estimate: Galerkin error is controlled by the error of any trial-space approximation. -/
theorem galerkin_error_le (S : Submodule ℝ V)
    {B : V →L[ℝ] V →L[ℝ] ℝ} {ℓ : V →L[ℝ] ℝ} {α : ℝ} (hα : 0 < α)
    (hcoercive : ∀ v, α * ‖v‖ * ‖v‖ ≤ B v v)
    {u uh : V} (hu : IsVariationalSolution B ℓ u) (hmem : uh ∈ S)
    (huh : ∀ v ∈ S, B uh v = ℓ v) (v : V) (hv : v ∈ S) :
    ‖u - uh‖ ≤ (‖B‖ / α) * ‖u - v‖ := by
  have horth := galerkin_orthogonality S hu huh (v - uh) (S.sub_mem hv hmem)
  have heq : B (u - uh) (u - uh) = B (u - uh) (u - v) := by
    calc
      B (u - uh) (u - uh) = B (u - uh) ((u - v) + (v - uh)) := by
        congr 1
        abel
      _ = B (u - uh) (u - v) := by rw [map_add, horth, add_zero]
  have hbound : α * ‖u - uh‖ * ‖u - uh‖ ≤ (‖B‖ * ‖u - uh‖) * ‖u - v‖ := by
    calc
      α * ‖u - uh‖ * ‖u - uh‖ ≤ B (u - uh) (u - uh) := hcoercive _
      _ = B (u - uh) (u - v) := heq
      _ ≤ ‖B (u - uh) (u - v)‖ := le_abs_self _
      _ ≤ ‖B (u - uh)‖ * ‖u - v‖ := (B (u - uh)).le_opNorm _
      _ ≤ (‖B‖ * ‖u - uh‖) * ‖u - v‖ :=
        mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _)
  by_cases hz : ‖u - uh‖ = 0
  · rw [hz]
    positivity
  · have hp : 0 < ‖u - uh‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have he : α * ‖u - uh‖ ≤ ‖B‖ * ‖u - v‖ := by nlinarith
    calc
      ‖u - uh‖ ≤ (‖B‖ * ‖u - v‖) / α := (le_div_iff₀ hα).mpr (by nlinarith)
      _ = (‖B‖ / α) * ‖u - v‖ := by ring

end PDE
