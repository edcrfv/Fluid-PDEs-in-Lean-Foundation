import PDE

/-! Public API examples, including the full three-dimensional Poisson weak equation. -/

open InnerProductSpace
open scoped ENNReal

section Variational

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

-- A coercive form supplies a solution for an arbitrary continuous load.
example (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (ℓ : V →L[ℝ] ℝ) :
    ∃ u, PDE.IsVariationalSolution B ℓ u :=
  (PDE.exists_unique_variationalSolution B hB ℓ).exists

-- The variational predicate has concrete solutions: the inner-product equation with load f.
example (f : V) : PDE.IsVariationalSolution (innerSL ℝ) (innerSL ℝ f) f :=
  fun _ => rfl

end Variational

-- Weak derivatives of a linear combination can be assembled without selecting a canonical one.
example {n : ℕ} (i : Fin n) {u du v dv : PDE.Space n → ℝ}
    (hu : PDE.HasWeakPartial i u du) (hv : PDE.HasWeakPartial i v dv) (a b : ℝ) :
    PDE.HasWeakPartial i (a • u + b • v) (a • du + b • dv) :=
  (hu.smul a).add (hv.smul b)

example {n : ℕ} {p : ℝ≥0∞} {u v : PDE.Space n → ℝ}
    (hu : PDE.MemW1p p u) (hv : PDE.MemW1p p v) : PDE.MemW1p p (u + v) :=
  hu.add hv

section ConcretePoisson

open PDE MeasureTheory
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000 in
example (Ω : Set (Space 3)) (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (f : DomainL2 Ω) :
    ∃ u : H10 Ω hΩ,
      (∀ v : H10 Ω hΩ, (∑ i : Fin 3, ∫ x in Ω,
        H1.derivative Ω i u.val x * H1.derivative Ω i v.val x) =
          ∫ x in Ω, f x * H1.value Ω v.val x) ∧ ‖u‖ ≤ poissonEnergyConstant Ω * ‖f‖ := by
  obtain ⟨u, hu, _⟩ := exists_unique_weakPoissonSolution (by decide : 2 < 3) hΩ hb f
  exact ⟨u, (isWeakPoissonSolution_iff f u).mp hu, hu.norm_le (by decide) hb⟩

end ConcretePoisson

section IntegratedHeat

open PDE MeasureTheory Set
set_option backward.isDefEq.respectTransparency false

-- Unlike the current Poisson coercivity proof, the integrated heat construction also
-- covers dimension two and requires neither boundedness nor boundary regularity.
set_option maxHeartbeats 1000000 in
example (Ω : Set (Space 2)) (hΩ : IsOpen Ω) (f : DomainL2 Ω) {T : ℝ} (hT : 0 ≤ T) :
    ∃ u : HeatEnergySpace Ω hΩ T,
      (∀ (η η' : ℝ → ℝ), (∀ t, HasDerivAt η (η' t) t) → Continuous η' → η T = 0 →
        ∀ v : H10 Ω hΩ,
          (∫ t in Icc (0 : ℝ) T, η' t * inner ℝ (H10.value Ω hΩ v) (H10.value Ω hΩ (u t))) -
          (∫ t in Icc (0 : ℝ) T, η t * dirichletForm Ω hΩ v (u t)) =
            -η 0 * inner ℝ f (H10.value Ω hΩ v)) ∧ ‖u‖ ≤ Real.sqrt (T + 1 / 2) * ‖f‖ := by
  obtain ⟨u, hu, _⟩ := exists_unique_integrated_weakHeatSolution Ω hΩ f hT
  exact ⟨u, hu, hu.norm_le hT⟩

end IntegratedHeat
