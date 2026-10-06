import PDE.ContinuityEquation
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Conservative and material momentum

The flux is `ρ u ⊗ u`, with its factors ordered to expose the product rule.
The identity includes the mass residual explicitly. Under conservation of mass it
vanishes, without dividing by density, so the result also allows vacuum points.
In the equation equivalence, `F` denotes force per unit volume.
-/

namespace PDE

variable {n : ℕ}

noncomputable def momentumFlux (ρ : ℝ → Space n → ℝ)
    (u : ℝ → Space n → Space n) (t : ℝ) (x : Space n) (i j : Fin n) : ℝ :=
  u t x i * (ρ t x * u t x j)

noncomputable def conservativeMomentum (ρ : ℝ → Space n → ℝ)
    (u : ℝ → Space n → Space n) (t : ℝ) (x : Space n) (i : Fin n) : ℝ :=
  timeDerivative (fun s y => ρ s y * u s y i) t x +
    tensorDivergence (momentumFlux ρ u t) x i

noncomputable def materialAcceleration (u : ℝ → Space n → Space n)
    (t : ℝ) (x : Space n) (i : Fin n) : ℝ :=
  materialDerivative u (fun s y => u s y i) t x

/-- Full momentum product rule, retaining the continuity residual. -/
theorem conservativeMomentum_eq_material_add_continuity
    {ρ : ℝ → Space n → ℝ} {u : ℝ → Space n → Space n} {t : ℝ} {x : Space n}
    (hρt : DifferentiableAt ℝ (fun s => ρ s x) t)
    (hut : ∀ i, DifferentiableAt ℝ (fun s => u s x i) t)
    (hρx : DifferentiableAt ℝ (ρ t) x)
    (hux : ∀ i, DifferentiableAt ℝ (fun y => u t y i) x) :
    conservativeMomentum ρ u t x = fun i =>
      ρ t x * materialAcceleration u t x i + u t x i * continuityResidual ρ u t x := by
  funext i
  have hflux : tensorDivergence (momentumFlux ρ u t) x i =
      ρ t x * advection (u t) (fun y => u t y i) x +
        u t x i * divergence (fun y j => ρ t y * u t y j) x := by
    change divergence (fun y j => u t y i * (ρ t y * u t y j)) x = _
    rw [divergence_mul (u := fun y j => ρ t y * u t y j)
      (hux i) (fun j => hρx.mul (hux j))]
    simp only [advection, Finset.mul_sum, mul_assoc]
  simp only [conservativeMomentum, timeDerivative, deriv_fun_mul hρt (hut i), hflux,
    materialAcceleration, materialDerivative, continuityResidual]
  ring

theorem conservativeMomentum_eq_of_continuity
    {ρ : ℝ → Space n → ℝ} {u : ℝ → Space n → Space n} {t : ℝ} {x : Space n}
    (hρt : DifferentiableAt ℝ (fun s => ρ s x) t)
    (hut : ∀ i, DifferentiableAt ℝ (fun s => u s x i) t)
    (hρx : DifferentiableAt ℝ (ρ t) x)
    (hux : ∀ i, DifferentiableAt ℝ (fun y => u t y i) x)
    (hmass : SatisfiesContinuityAt ρ u t x) :
    conservativeMomentum ρ u t x = fun i => ρ t x * materialAcceleration u t x i := by
  rw [conservativeMomentum_eq_material_add_continuity hρt hut hρx hux]
  simp only [SatisfiesContinuityAt] at hmass
  simp only [hmass, mul_zero, add_zero]

theorem momentum_equation_iff_material
    {ρ : ℝ → Space n → ℝ} {u : ℝ → Space n → Space n} {t : ℝ} {x : Space n}
    (hρt : DifferentiableAt ℝ (fun s => ρ s x) t)
    (hut : ∀ i, DifferentiableAt ℝ (fun s => u s x i) t)
    (hρx : DifferentiableAt ℝ (ρ t) x)
    (hux : ∀ i, DifferentiableAt ℝ (fun y => u t y i) x)
    (hmass : SatisfiesContinuityAt ρ u t x) (F : Space n) :
    conservativeMomentum ρ u t x = F ↔
      (fun i => ρ t x * materialAcceleration u t x i) = F := by
  rw [conservativeMomentum_eq_of_continuity hρt hut hρx hux hmass]

end PDE
