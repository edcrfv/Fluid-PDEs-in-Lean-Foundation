import PDE.MaterialDerivative

/-!
# Two forms of conservation of mass

The conservative residual is `∂ₜρ + div(ρu)`; the material residual is
`Dₜρ + ρ div u`. The spatial product rule identifies them pointwise.
-/

namespace PDE

variable {n : ℕ}

noncomputable def continuityResidual (ρ : ℝ → Space n → ℝ)
    (u : ℝ → Space n → Space n) (t : ℝ) (x : Space n) : ℝ :=
  timeDerivative ρ t x + divergence (fun y i => ρ t y * u t y i) x

def SatisfiesContinuityAt (ρ : ℝ → Space n → ℝ)
    (u : ℝ → Space n → Space n) (t : ℝ) (x : Space n) : Prop :=
  continuityResidual ρ u t x = 0

theorem continuityResidual_eq_material {ρ : ℝ → Space n → ℝ}
    {u : ℝ → Space n → Space n} {t : ℝ} {x : Space n}
    (hρ : DifferentiableAt ℝ (ρ t) x)
    (hu : ∀ i, DifferentiableAt ℝ (fun y => u t y i) x) :
    continuityResidual ρ u t x =
      materialDerivative u ρ t x + ρ t x * divergence (u t) x := by
  rw [continuityResidual, divergence_mul hρ hu, materialDerivative]
  ring

/-- Equivalence of the two classical mass equations; time differentiability is explicit. -/
theorem satisfiesContinuityAt_iff_material {ρ : ℝ → Space n → ℝ}
    {u : ℝ → Space n → Space n} {t : ℝ} {x : Space n}
    (_hρt : DifferentiableAt ℝ (fun s => ρ s x) t)
    (hρ : DifferentiableAt ℝ (ρ t) x)
    (hu : ∀ i, DifferentiableAt ℝ (fun y => u t y i) x) :
    SatisfiesContinuityAt ρ u t x ↔
      materialDerivative u ρ t x + ρ t x * divergence (u t) x = 0 := by
  rw [SatisfiesContinuityAt, continuityResidual_eq_material hρ hu]

/-- Materially constant, nonzero density and mass conservation imply zero divergence. -/
theorem divergence_eq_zero_of_material_density_constant {ρ : ℝ → Space n → ℝ}
    {u : ℝ → Space n → Space n} {t : ℝ} {x : Space n}
    (hρ : DifferentiableAt ℝ (ρ t) x)
    (hu : ∀ i, DifferentiableAt ℝ (fun y => u t y i) x)
    (hmass : SatisfiesContinuityAt ρ u t x)
    (hmaterial : materialDerivative u ρ t x = 0) (hne : ρ t x ≠ 0) :
    divergence (u t) x = 0 := by
  have h := (continuityResidual_eq_material hρ hu).symm.trans hmass
  rw [hmaterial, zero_add] at h
  exact (mul_eq_zero.mp h).resolve_left hne

end PDE
