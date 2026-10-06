import PDE.WeakDerivative
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Algebra.BigOperators.Pi

/-!
# Coordinate calculus for smooth fluid identities

Coordinates use the existing `Space n`. Its ambient norm is the supremum norm;
the physical dot product below is explicitly the sum of coordinate products.
Tensor divergence differentiates the second index: `(div A)ᵢ = ∑ⱼ ∂ⱼ Aᵢⱼ`.
-/

open scoped BigOperators

namespace PDE

variable {n : ℕ}

/-- The physical Euclidean dot product, independent of the ambient norm on `Space n`. -/
def fluidDot (u v : Space n) : ℝ := ∑ i, u i * v i

noncomputable def divergence (u : Space n → Space n) (x : Space n) : ℝ :=
  ∑ i, coordDeriv i (fun y => u y i) x

noncomputable def advection (u : Space n → Space n) (f : Space n → ℝ)
    (x : Space n) : ℝ := ∑ i, u x i * coordDeriv i f x

noncomputable def tensorDivergence (A : Space n → Fin n → Fin n → ℝ)
    (x : Space n) (i : Fin n) : ℝ :=
  ∑ j, coordDeriv j (fun y => A y i j) x

noncomputable def laplacian (f : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i, coordDeriv i (coordDeriv i f) x

theorem coordDeriv_add {f g : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    coordDeriv i (fun y => f y + g y) x = coordDeriv i f x + coordDeriv i g x := by
  simp [coordDeriv, fderiv_fun_add hf hg]

theorem coordDeriv_mul {f g : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    coordDeriv i (fun y => f y * g y) x =
      f x * coordDeriv i g x + g x * coordDeriv i f x := by
  simp [coordDeriv, fderiv_fun_mul hf hg]

theorem coordDeriv_const_mul {f : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) (i : Fin n) :
    coordDeriv i (fun y => c * f y) x = c * coordDeriv i f x := by
  rw [coordDeriv_mul (differentiableAt_const c) hf]
  simp [coordDeriv]

theorem coordDeriv_sum {ι : Type*} (s : Finset ι) {f : ι → Space n → ℝ}
    {x : Space n} (hf : ∀ k ∈ s, DifferentiableAt ℝ (f k) x) (i : Fin n) :
    coordDeriv i (fun y => ∑ k ∈ s, f k y) x = ∑ k ∈ s, coordDeriv i (f k) x := by
  simp [coordDeriv, fderiv_fun_sum hf]

/-- A directional Fréchet derivative is the sum of its coordinate derivatives. -/
theorem fderiv_eq_sum_coordDeriv (f : Space n → ℝ) (x v : Space n) :
    fderiv ℝ f x v = ∑ i, v i * coordDeriv i f x := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp [coordDeriv]

theorem advection_eq_fderiv (u : Space n → Space n) (f : Space n → ℝ) (x : Space n) :
    advection u f x = fderiv ℝ f x (u x) :=
  (fderiv_eq_sum_coordDeriv f x (u x)).symm

/-- The spatial product rule for a scalar times a vector field. -/
theorem divergence_mul {ρ : Space n → ℝ} {u : Space n → Space n} {x : Space n}
    (hρ : DifferentiableAt ℝ ρ x)
    (hu : ∀ i, DifferentiableAt ℝ (fun y => u y i) x) :
    divergence (fun y i => ρ y * u y i) x =
      advection u ρ x + ρ x * divergence u x := by
  simp only [divergence, advection, coordDeriv_mul hρ (hu _),
    Finset.sum_add_distrib, Finset.mul_sum]
  ring

end PDE
