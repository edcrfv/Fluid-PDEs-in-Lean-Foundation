import PDE.LaxMilgram
import PDE.Poincare

/-!
# Homogeneous Dirichlet Poisson weak solutions

On a bounded open domain in dimension n ≥ 3, every L² load has a unique H₀¹ weak
solution of -Δu = f. The function space, coercivity, load continuity and energy bound
are all constructed here or in the Sobolev modules. The weak equation uses every
H₀¹ test function. Interior and boundary regularity are separate later theorems.
-/

open MeasureTheory InnerProductSpace Set
open scoped ENNReal

namespace PDE

variable {n : ℕ} {Ω : Set (Space n)} {hΩ : IsOpen Ω}

-- Nested submodule norms are definitionally equal through the Sobolev graph definitions.
-- Allow the elaborator to unfold those definitions when matching continuous linear maps.
set_option backward.isDefEq.respectTransparency false

/-- The weak gradient, bundled in a finite Hilbert product of L² spaces. -/
noncomputable def H10.gradient (Ω : Set (Space n)) (hΩ : IsOpen Ω) :
    H10 Ω hΩ →L[ℝ] PiLp 2 (fun _ : Fin n => DomainL2 Ω) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => DomainL2 Ω)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (H1.derivative Ω i).comp (H10.toH1 Ω hΩ))

theorem H10.gradient_apply (u : H10 Ω hΩ) (i : Fin n) :
    H10.gradient Ω hΩ u i = H1.derivative Ω i u.val := rfl

/-- The sum of coordinate gradient pairings as a bounded bilinear form. -/
noncomputable def dirichletForm (Ω : Set (Space n)) (hΩ : IsOpen Ω) :
    H10 Ω hΩ →L[ℝ] H10 Ω hΩ →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (H10.gradient Ω hΩ) (H10.gradient Ω hΩ)

theorem dirichletForm_apply (u v : H10 Ω hΩ) :
    dirichletForm Ω hΩ u v = ∑ i : Fin n,
      inner ℝ (H1.derivative Ω i u.val) (H1.derivative Ω i v.val) := by
  exact PiLp.inner_apply (H10.gradient Ω hΩ u) (H10.gradient Ω hΩ v)

theorem dirichletForm_integral (u v : H10 Ω hΩ) :
    dirichletForm Ω hΩ u v = ∑ i : Fin n,
      ∫ x in Ω, H1.derivative Ω i u.val x * H1.derivative Ω i v.val x := by
  rw [dirichletForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  simp [mul_comm]

theorem dirichletForm_self (u : H10 Ω hΩ) :
    dirichletForm Ω hΩ u u = ∑ i : Fin n, ‖H1.derivative Ω i u.val‖ ^ 2 := by
  simp only [dirichletForm_apply, real_inner_self_eq_norm_sq]

/-- The L² forcing paired with the value of a zero-boundary Sobolev test. -/
noncomputable def poissonLoad (Ω : Set (Space n)) (hΩ : IsOpen Ω) (f : DomainL2 Ω) :
    H10 Ω hΩ →L[ℝ] ℝ :=
  (innerSL ℝ f).comp ((H1.value Ω).comp (H10.toH1 Ω hΩ))

theorem poissonLoad_integral (f : DomainL2 Ω) (v : H10 Ω hΩ) :
    poissonLoad Ω hΩ f v = ∫ x in Ω, f x * H1.value Ω v.val x := by
  change inner ℝ f (H1.value Ω v.val) = _
  rw [L2.inner_def]
  simp [mul_comm]

theorem poissonLoad_norm_le (f : DomainL2 Ω) : ‖poissonLoad Ω hΩ f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  change ‖inner ℝ f (H1.value Ω v.val)‖ ≤ ‖f‖ * ‖v‖
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (H1.norm_value_le v.val) (norm_nonneg _))

/-- A finite explicit bound in terms of Mathlib's domain-dependent Sobolev constant. -/
noncomputable def poissonEnergyConstant (Ω : Set (Space n)) : ℝ :=
  (poincareConstant Ω : ℝ) ^ 2 * n + 1

theorem poissonEnergyConstant_pos (Ω : Set (Space n)) : 0 < poissonEnergyConstant Ω := by
  unfold poissonEnergyConstant
  positivity

/-- The full Sobolev norm is controlled by the Dirichlet energy. -/
theorem norm_sq_le_dirichletForm (hn : 2 < n) (hb : Bornology.IsBounded Ω)
    (u : H10 Ω hΩ) : ‖u‖ ^ 2 ≤ poissonEnergyConstant Ω * dirichletForm Ω hΩ u u := by
  have hp := u.poincare hn hb
  have hsq : ‖H1.value Ω u.val‖ ^ 2 ≤
      (poincareConstant Ω : ℝ) ^ 2 * (∑ i : Fin n, ‖H1.derivative Ω i u.val‖) ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hp 2
  have hsum : (∑ i : Fin n, ‖H1.derivative Ω i u.val‖) ^ 2 ≤
      (n : ℝ) * ∑ i : Fin n, ‖H1.derivative Ω i u.val‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin n => (1 : ℝ)) (fun i => ‖H1.derivative Ω i u.val‖)
  have hvalue := hsq.trans (mul_le_mul_of_nonneg_left hsum (sq_nonneg _))
  rw [dirichletForm_self]
  change ‖u.val‖ ^ 2 ≤ _
  rw [H1.norm_sq_eq]
  unfold poissonEnergyConstant
  nlinarith

theorem dirichletForm_coercive_bound (hn : 2 < n) (hb : Bornology.IsBounded Ω)
    (u : H10 Ω hΩ) :
    (poissonEnergyConstant Ω)⁻¹ * ‖u‖ * ‖u‖ ≤ dirichletForm Ω hΩ u u := by
  calc
    (poissonEnergyConstant Ω)⁻¹ * ‖u‖ * ‖u‖ = ‖u‖ ^ 2 / poissonEnergyConstant Ω := by ring
    _ ≤ dirichletForm Ω hΩ u u := (div_le_iff₀ (poissonEnergyConstant_pos Ω)).mpr
      (by simpa only [mul_comm] using norm_sq_le_dirichletForm hn hb u)

theorem dirichletForm_isCoercive (hn : 2 < n) (hb : Bornology.IsBounded Ω) :
    IsCoercive (dirichletForm Ω hΩ) :=
  ⟨_, inv_pos.mpr (poissonEnergyConstant_pos Ω), dirichletForm_coercive_bound hn hb⟩

/-- The homogeneous Dirichlet weak Poisson equation, tested against the whole energy space. -/
def IsWeakPoissonSolution (f : DomainL2 Ω) (u : H10 Ω hΩ) : Prop :=
  IsVariationalSolution (V := H10 Ω hΩ) (dirichletForm Ω hΩ) (poissonLoad Ω hΩ f) u

set_option maxHeartbeats 1000000 in
theorem isWeakPoissonSolution_iff (f : DomainL2 Ω) (u : H10 Ω hΩ) :
    IsWeakPoissonSolution f u ↔ ∀ v : H10 Ω hΩ,
      (∑ i : Fin n, ∫ x in Ω,
        H1.derivative Ω i u.val x * H1.derivative Ω i v.val x) =
          ∫ x in Ω, f x * H1.value Ω v.val x := by
  simp only [IsWeakPoissonSolution, IsVariationalSolution, dirichletForm_integral,
    poissonLoad_integral]

set_option maxHeartbeats 1000000 in
/-- Concrete Poisson existence and uniqueness, with no assumed existence premise. -/
theorem exists_unique_weakPoissonSolution (hn : 2 < n) (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (f : DomainL2 Ω) :
    ∃! u : H10 Ω hΩ, IsWeakPoissonSolution f u := by
  unfold IsWeakPoissonSolution
  exact exists_unique_variationalSolution (V := H10 Ω hΩ)
    (dirichletForm Ω hΩ) (dirichletForm_isCoercive hn hb) (poissonLoad Ω hΩ f)

theorem IsWeakPoissonSolution.norm_le (hn : 2 < n) (hb : Bornology.IsBounded Ω)
    {f : DomainL2 Ω} {u : H10 Ω hΩ} (hu : IsWeakPoissonSolution f u) :
    ‖u‖ ≤ poissonEnergyConstant Ω * ‖f‖ := by
  have he := IsVariationalSolution.norm_le hu (inv_pos.mpr (poissonEnergyConstant_pos Ω))
    (dirichletForm_coercive_bound hn hb)
  calc
    ‖u‖ ≤ ‖poissonLoad Ω hΩ f‖ / (poissonEnergyConstant Ω)⁻¹ := he
    _ = poissonEnergyConstant Ω * ‖poissonLoad Ω hΩ f‖ := by rw [div_inv_eq_mul, mul_comm]
    _ ≤ poissonEnergyConstant Ω * ‖f‖ :=
      mul_le_mul_of_nonneg_left (poissonLoad_norm_le f) (poissonEnergyConstant_pos Ω).le

end PDE
