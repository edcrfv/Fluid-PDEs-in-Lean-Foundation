import PDE.EllipticWeakSolutions
import PDE.SobolevCompactness
import PDE.GalerkinConvergence

/-!
# Concrete convergent Dirichlet Poisson approximations

The trial spaces, finite-dimensional solutions and their H¹ convergence are all produced
from the actual Sobolev energy space. The discrete equations use `dirichletForm` and
`poissonLoad`, whose integral identities are proved in `EllipticWeakSolutions`.
-/

open MeasureTheory InnerProductSpace Filter Set
open scoped Topology
namespace PDE
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000 in
/-- Actual finite-dimensional Poisson approximations converge in the full H¹ energy norm. -/
theorem exists_poisson_galerkin_sequence {n : ℕ} (hn : 2 < n) {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (f : DomainL2 Ω) :
    ∃ S : ℕ → Submodule ℝ (H10 Ω hΩ),
      (∀ k, FiniteDimensional ℝ (S k)) ∧ Monotone S ∧
      Dense (⋃ k, (S k : Set (H10 Ω hΩ))) ∧
      ∃ u : H10 Ω hΩ, IsWeakPoissonSolution f u ∧
        ∃ uh : ℕ → H10 Ω hΩ, (∀ k, uh k ∈ S k) ∧
          (∀ k v, v ∈ S k → dirichletForm Ω hΩ (uh k) v = poissonLoad Ω hΩ f v) ∧
            Tendsto uh atTop (𝓝 u) := by
  unfold IsWeakPoissonSolution
  exact exists_convergent_galerkin_sequence (V := H10 Ω hΩ)
    (dirichletForm Ω hΩ) (dirichletForm_isCoercive hn hb) (poissonLoad Ω hΩ f)
end PDE
