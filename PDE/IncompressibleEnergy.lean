import PDE.VectorCalculus
import PDE.ClassicalWeakDerivative

/-!
# Smooth incompressible convection does no total kinetic work

We work on all of `Space n` with Lebesgue measure. The advecting field is C¹ and
divergence-free; the transported field is C¹ with compact support. Integration by
parts proves cancellation, with integrability proved separately. Taking the two
fields equal gives the nonlinear incompressible convection cancellation.

This module does not assert a time-dependent energy identity for weak NS solutions.
-/

open MeasureTheory
open scoped BigOperators

namespace PDE

variable {n : ℕ}

theorem continuous_coordDeriv_of_one {f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin n) : Continuous (coordDeriv i f) :=
  (hf.continuous_fderiv (by simp)).clm_apply continuous_const

theorem integrable_mul_coordDeriv {f g : Space n → ℝ}
    (hf : Continuous f) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (i : Fin n) :
    Integrable (fun x => f x * coordDeriv i g x) :=
  (hf.mul (continuous_coordDeriv_of_one hg i)).integrable_of_hasCompactSupport
    (hgc.fderiv_apply ℝ (Pi.single i 1)).mul_left

theorem integrable_coordDeriv_mul {f g : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : Continuous g) (hgc : HasCompactSupport g) (i : Fin n) :
    Integrable (fun x => coordDeriv i f x * g x) :=
  ((continuous_coordDeriv_of_one hf i).mul hg).integrable_of_hasCompactSupport hgc.mul_left

theorem integrable_advection {u : Space n → Space n} {φ : Space n → ℝ}
    (hu : ∀ i, Continuous (fun x => u x i))
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) : Integrable (advection u φ) := by
  exact integrable_finsetSum Finset.univ fun i _ => integrable_mul_coordDeriv (hu i) hφ hφc i

/-- Spatial integration by parts, with all products integrable. -/
theorem integral_advection_eq_neg_divergence_mul
    {u : Space n → Space n} {φ : Space n → ℝ}
    (hu : ∀ i, ContDiff ℝ 1 (fun x => u x i))
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫ x, advection u φ x) = -(∫ x, divergence u x * φ x) := by
  have hleft (i : Fin n) := integrable_mul_coordDeriv (hu i).continuous hφ hφc i
  have hright (i : Fin n) := integrable_coordDeriv_mul (hu i) hφ.continuous hφc i
  have hip (i : Fin n) : (∫ x, u x i * coordDeriv i φ x) =
      -(∫ x, coordDeriv i (fun y => u y i) x * φ x) := by
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hright i) (hleft i)
      (((hu i).continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left)
      (fun x _ => (hu i).differentiable (by simp) x)
      (fun x _ => hφ.differentiable (by simp) x)
  simp only [advection, divergence, Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => hleft i),
    integral_finsetSum _ (fun i _ => hright i)]
  simp only [hip, Finset.sum_neg_distrib]

theorem integral_advection_eq_zero_of_divergence_zero
    {u : Space n → Space n} {φ : Space n → ℝ}
    (hu : ∀ i, ContDiff ℝ 1 (fun x => u x i))
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hdiv : ∀ x, divergence u x = 0) : (∫ x, advection u φ x) = 0 := by
  rw [integral_advection_eq_neg_divergence_mul hu hφ hφc]
  simp [hdiv]

/-- Kinetic energy per unit mass, expressed in physical coordinates. -/
noncomputable def kineticEnergy (v : Space n → Space n) (x : Space n) : ℝ :=
  ∑ i, (1 / 2 : ℝ) * (v x i * v x i)

theorem kineticEnergy_eq_half_dot (v : Space n → Space n) (x : Space n) :
    kineticEnergy v x = (1 / 2 : ℝ) * fluidDot (v x) (v x) := by
  simp only [kineticEnergy, fluidDot, Finset.mul_sum]

theorem contDiff_kineticEnergy {v : Space n → Space n}
    (hv : ∀ i, ContDiff ℝ 1 (fun x => v x i)) : ContDiff ℝ 1 (kineticEnergy v) :=
  ContDiff.sum fun i _ => contDiff_const.mul ((hv i).mul (hv i))

theorem hasCompactSupport_kineticEnergy {v : Space n → Space n}
    (hvc : HasCompactSupport v) : HasCompactSupport (kineticEnergy v) := by
  exact hvc.comp_left (g := fun z : Space n => ∑ i, (1 / 2 : ℝ) * (z i * z i)) (by simp)

theorem coordDeriv_kineticEnergy {v : Space n → Space n} {x : Space n}
    (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x) (j : Fin n) :
    coordDeriv j (kineticEnergy v) x =
      ∑ i, v x i * coordDeriv j (fun y => v y i) x := by
  unfold kineticEnergy
  rw [coordDeriv_sum Finset.univ (f := fun i y => (1 / 2 : ℝ) * (v y i * v y i))
    (fun i _ => ((hv i).mul (hv i)).const_mul (1 / 2 : ℝ))]
  apply Finset.sum_congr rfl
  intro i _
  have hmul : DifferentiableAt ℝ (fun y => v y i * v y i) x := (hv i).mul (hv i)
  rw [coordDeriv_const_mul hmul, coordDeriv_mul (hv i) (hv i)]
  ring

/-- The pointwise kinetic chain rule: `(u·∇v)·v = u·∇(|v|²/2)`. -/
theorem advection_kineticEnergy {v : Space n → Space n} {x : Space n}
    (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x) (u : Space n → Space n) :
    advection u (kineticEnergy v) x =
      fluidDot (fun i => advection u (fun y => v y i) x) (v x) := by
  simp only [advection, coordDeriv_kineticEnergy hv, fluidDot,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem integrable_kineticConvection {u v : Space n → Space n}
    (hu : ∀ i, Continuous (fun x => u x i))
    (hv : ∀ i, ContDiff ℝ 1 (fun x => v x i)) (hvc : HasCompactSupport v) :
    Integrable (fun x => fluidDot (fun i => advection u (fun y => v y i) x) (v x)) := by
  have heq : (fun x => fluidDot (fun i => advection u (fun y => v y i) x) (v x)) =
      advection u (kineticEnergy v) := by
    funext x
    exact (advection_kineticEnergy (fun i => (hv i).differentiable (by simp) x) u).symm
  rw [heq]
  exact integrable_advection hu (contDiff_kineticEnergy hv) (hasCompactSupport_kineticEnergy hvc)

/-- Divergence-free advection does no total kinetic work on a compactly supported field. -/
theorem integral_kineticConvection_eq_zero {u v : Space n → Space n}
    (hu : ∀ i, ContDiff ℝ 1 (fun x => u x i))
    (hv : ∀ i, ContDiff ℝ 1 (fun x => v x i)) (hvc : HasCompactSupport v)
    (hdiv : ∀ x, divergence u x = 0) :
    (∫ x, fluidDot (fun i => advection u (fun y => v y i) x) (v x)) = 0 := by
  have heq : (fun x => fluidDot (fun i => advection u (fun y => v y i) x) (v x)) =
      advection u (kineticEnergy v) := by
    funext x
    exact (advection_kineticEnergy (fun i => (hv i).differentiable (by simp) x) u).symm
  rw [heq]
  exact integral_advection_eq_zero_of_divergence_zero hu (contDiff_kineticEnergy hv)
    (hasCompactSupport_kineticEnergy hvc) hdiv

theorem incompressible_convection_energy_cancellation {u : Space n → Space n}
    (hu : ∀ i, ContDiff ℝ 1 (fun x => u x i)) (huc : HasCompactSupport u)
    (hdiv : ∀ x, divergence u x = 0) :
    (∫ x, fluidDot (fun i => advection u (fun y => u y i) x) (u x)) = 0 :=
  integral_kineticConvection_eq_zero hu hu huc hdiv

end PDE
