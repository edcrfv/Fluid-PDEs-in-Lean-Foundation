import PDE.LaxMilgram
import Mathlib.Analysis.Normed.Module.FiniteDimension
/-!
# Finite-dimensional mass forms

An injective map into the physical Hilbert space induces a coercive mass form on a
finite-dimensional trial space. This distinguishes the L² time pairing from the H¹
norm used to construct the trial space, and supplies the invertible mass operator.
-/

open InnerProductSpace
namespace PDE
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The mass form induced by an embedding into the physical L² Hilbert space. -/
noncomputable def massForm (J : V →L[ℝ] H) : V →L[ℝ] V →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp J J

theorem massForm_apply (J : V →L[ℝ] H) (u v : V) :
    massForm J u v = inner ℝ (J u) (J v) := rfl

/-- Every injective finite-dimensional mass embedding gives an invertible coercive mass form. -/
theorem massForm_isCoercive [FiniteDimensional ℝ V] (J : V →L[ℝ] H)
    (hJ : Function.Injective J) : IsCoercive (massForm J) := by
  obtain ⟨K, hK, hLip⟩ := J.toLinearMap.injective_iff_antilipschitz.mp hJ
  have hKreal : 0 < (K : ℝ) := hK
  refine ⟨((K : ℝ) ^ 2)⁻¹, by positivity, fun v => ?_⟩
  have hb : ‖v‖ ≤ K * ‖J v‖ := ZeroHomClass.bound_of_antilipschitz J hLip v
  have hs : ‖v‖ ^ 2 ≤ (K : ℝ) ^ 2 * ‖J v‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [massForm_apply, real_inner_self_eq_norm_sq]
  calc
    ((K : ℝ) ^ 2)⁻¹ * ‖v‖ * ‖v‖ = ‖v‖ ^ 2 / (K : ℝ) ^ 2 := by ring
    _ ≤ ‖J v‖ ^ 2 := (div_le_iff₀ (sq_pos_of_pos hKreal)).mpr (by nlinarith)
end PDE
