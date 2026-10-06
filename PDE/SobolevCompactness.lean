import PDE.SobolevZero
import PDE.WeakCompactness
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Weak subsequences in the Sobolev energy space

Restricted Lebesgue measure is separable and L² has finite exponent, so the finite L² graph
and its subspaces are second-countable. The abstract Hilbert extraction theorem therefore
applies to the actual H₀¹ space without adding a separability hypothesis to each PDE proof.
This is weak H¹ compactness, not a strong L²/Rellich theorem.
-/

open MeasureTheory InnerProductSpace Filter
open scoped ENNReal Topology

namespace PDE

instance domainL2SecondCountable {n : ℕ} (Ω : Set (Space n)) :
    SecondCountableTopology (DomainL2 Ω) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  exact inferInstanceAs (SecondCountableTopology (Lp ℝ 2 (volume.restrict Ω)))

set_option backward.isDefEq.respectTransparency false in
/-- A bounded sequence in the actual zero-boundary energy space admits a weak subsequence. -/
theorem H10.exists_weakly_convergent_subsequence {n : ℕ} {Ω : Set (Space n)}
    {hΩ : IsOpen Ω} (u : ℕ → H10 Ω hΩ) {C : ℝ} (hC : ∀ k, ‖u k‖ ≤ C) :
    ∃ v : H10 Ω hΩ, ‖v‖ ≤ C ∧ ∃ r : ℕ → ℕ, StrictMono r ∧
      ∀ w : H10 Ω hΩ,
        Tendsto (fun k => inner ℝ (u (r k)) w) atTop (𝓝 (inner ℝ v w)) :=
  PDE.exists_weakly_convergent_subsequence (V := H10 Ω hΩ) u hC

end PDE
