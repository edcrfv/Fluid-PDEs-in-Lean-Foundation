import PDE.VectorCalculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Divergence of constant-viscosity Newtonian stress

`τᵢⱼ = μ(∂ⱼuᵢ + ∂ᵢuⱼ) + λ δᵢⱼ div u`, with arbitrary real constants `μ, λ`.
For a C² velocity this gives `div τ = μ Δu + (λ + μ) grad(div u)`.
No Stokes hypothesis or dimension-dependent relation between the viscosities is assumed.
-/

open scoped BigOperators

namespace PDE

variable {n : ℕ}

theorem contDiff_coordDeriv_of_two {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin n) :
    ContDiff ℝ 1 (coordDeriv i f) :=
  (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiff_const

/-- Equality of mixed coordinate derivatives follows from C² regularity. -/
theorem coordDeriv_coordDeriv_comm {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (i j : Fin n) (x : Space n) :
    coordDeriv i (coordDeriv j f) x = coordDeriv j (coordDeriv i f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by simp) x
  have hsym : IsSymmSndFDerivAt ℝ f x := hf.contDiffAt.isSymmSndFDerivAt (by simp)
  change (fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) x) (Pi.single i 1) =
    (fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x) (Pi.single j 1)
  simpa [fderiv_clm_apply hd (differentiableAt_const _)] using
    hsym.eq (Pi.single i 1) (Pi.single j 1)

noncomputable def newtonianStress (μ lam : ℝ) (u : Space n → Space n)
    (x : Space n) (i j : Fin n) : ℝ :=
  μ * (coordDeriv j (fun y => u y i) x + coordDeriv i (fun y => u y j) x) +
    lam * (if i = j then divergence u x else 0)

theorem divergence_differentiable_of_two {u : Space n → Space n}
    (hu : ∀ i, ContDiff ℝ 2 (fun y => u y i)) : Differentiable ℝ (divergence u) := by
  intro x
  exact DifferentiableAt.fun_sum fun i _ =>
    (contDiff_coordDeriv_of_two (hu i) i).differentiable (by simp) x

/-- The actual coordinate derivative of Newtonian stress, including mixed partial symmetry. -/
theorem tensorDivergence_newtonianStress {u : Space n → Space n}
    (hu : ∀ i, ContDiff ℝ 2 (fun y => u y i)) (μ lam : ℝ) (x : Space n) (i : Fin n) :
    tensorDivergence (newtonianStress μ lam u) x i =
      μ * laplacian (fun y => u y i) x + (lam + μ) * coordDeriv i (divergence u) x := by
  have hd (j k : Fin n) : DifferentiableAt ℝ (coordDeriv j (fun y => u y k)) x :=
    (contDiff_coordDeriv_of_two (hu k) j).differentiable (by simp) x
  have hdiv := divergence_differentiable_of_two hu x
  have hdiag (j : Fin n) :
      coordDeriv j (fun y => lam * (if i = j then divergence u y else 0)) x =
        if i = j then lam * coordDeriv j (divergence u) x else 0 := by
    split_ifs with hij
    · exact coordDeriv_const_mul hdiv lam j
    · simp [coordDeriv]
  have hentry (j : Fin n) :
      coordDeriv j (fun y => newtonianStress μ lam u y i j) x =
        μ * (coordDeriv j (coordDeriv j (fun y => u y i)) x +
          coordDeriv i (coordDeriv j (fun y => u y j)) x) +
        (if i = j then lam * coordDeriv j (divergence u) x else 0) := by
    have hdi : DifferentiableAt ℝ (fun y => if i = j then divergence u y else 0) x := by
      split_ifs
      · exact hdiv
      · exact differentiableAt_const _
    have hadd : DifferentiableAt ℝ
        (fun y => coordDeriv j (fun y => u y i) y + coordDeriv i (fun y => u y j) y) x :=
      (hd j i).add (hd i j)
    simp only [newtonianStress]
    rw [coordDeriv_add (hadd.const_mul μ)
      (hdi.const_mul lam), coordDeriv_const_mul hadd,
      coordDeriv_add (hd j i) (hd i j), hdiag,
      coordDeriv_coordDeriv_comm (hu j) j i]
  have hgrad : coordDeriv i (divergence u) x =
      ∑ j, coordDeriv i (coordDeriv j (fun y => u y j)) x :=
    coordDeriv_sum Finset.univ (fun j _ => hd j j) i
  simp only [tensorDivergence, hentry, Finset.sum_add_distrib, mul_add,
    ← Finset.mul_sum, laplacian]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← hgrad]
  ring

/-- For a globally divergence-free C² velocity, only the vector Laplacian remains. -/
theorem tensorDivergence_newtonianStress_of_divergence_zero {u : Space n → Space n}
    (hu : ∀ i, ContDiff ℝ 2 (fun y => u y i))
    (hdiv : ∀ x, divergence u x = 0) (μ lam : ℝ) (x : Space n) (i : Fin n) :
    tensorDivergence (newtonianStress μ lam u) x i =
      μ * laplacian (fun y => u y i) x := by
  rw [tensorDivergence_newtonianStress hu μ lam x i]
  have heq : divergence u = fun _ => 0 := funext hdiv
  simp [heq, coordDeriv]

end PDE
