import PDE.HeatBochner

/-!
# Time integration by parts for heat Galerkin trajectories

The product rule and fundamental theorem of calculus yield the integrated equation.
Orthogonality of the initial mass projection identifies its pairing with the original
L² initial datum for every trial-space test.
-/

open InnerProductSpace MeasureTheory Set Filter
open scoped Topology ENNReal
namespace PDE
variable {n : ℕ} {Ω : Set (Space n)} {hΩ : IsOpen Ω}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] trialNormedAddCommGroup trialSeminormedAddCommGroup
  trialNormedSpace trialInnerProductSpace trialDualTopology

theorem dirichletForm_symm (u v : H10 Ω hΩ) :
    dirichletForm Ω hΩ u v = dirichletForm Ω hΩ v u := by
  change inner ℝ (H10.gradient Ω hΩ u) (H10.gradient Ω hΩ v) =
    inner ℝ (H10.gradient Ω hΩ v) (H10.gradient Ω hΩ u)
  exact real_inner_comm _ _

/-- Time integration by parts for each finite heat equation, with the projected initial
pairing replaced by the original L² datum using orthogonality. -/
theorem heatGalerkin_integrated_weakEquation (S : Submodule ℝ (H10 Ω hΩ))
    [FiniteDimensional ℝ S] (f : DomainL2 Ω) (v : S)
    (η η' : ℝ → ℝ) (hη : ∀ t, HasDerivAt η (η' t) t) (hη' : Continuous η')
    {T : ℝ} (hηT : η T = 0) :
    (∫ t in (0 : ℝ)..T, η' t * inner ℝ (H10.value Ω hΩ v.val)
      (H10.value Ω hΩ (heatTrajectory S f t))) -
    (∫ t in (0 : ℝ)..T, η t * dirichletForm Ω hΩ v.val (heatTrajectory S f t)) =
      -η 0 * inner ℝ f (H10.value Ω hΩ v.val) := by
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun t => (hη t).continuousAt
  have hu := heatTrajectory_continuous S f
  have hm : Continuous (fun t => inner ℝ (H10.value Ω hΩ v.val)
      (H10.value Ω hΩ (heatTrajectory S f t))) :=
    continuous_const.inner ((H10.value Ω hΩ).continuous.comp hu)
  have hb : Continuous (fun t => dirichletForm Ω hΩ v.val (heatTrajectory S f t)) :=
    (dirichletForm Ω hΩ v.val).continuous.comp hu
  have hmass (t : ℝ) : HasDerivAt
      (fun t => inner ℝ (H10.value Ω hΩ v.val) (H10.value Ω hΩ (heatTrajectory S f t)))
      (-dirichletForm Ω hΩ v.val (heatTrajectory S f t)) t := by
    have h := heatGalerkin_weakEquation S (heatInitialProjection S f) v t
    change HasDerivAt
      (fun t => inner ℝ (H10.value Ω hΩ (heatTrajectory S f t)) (H10.value Ω hΩ v.val))
      (-dirichletForm Ω hΩ (heatTrajectory S f t) v.val) t at h
    have he (x : H10 Ω hΩ) : inner ℝ (H10.value Ω hΩ x) (H10.value Ω hΩ v.val) =
        inner ℝ (H10.value Ω hΩ v.val) (H10.value Ω hΩ x) := real_inner_comm _ _
    simpa only [he, dirichletForm_symm (heatTrajectory S f t) v.val] using h
  have hprod (t : ℝ) : HasDerivAt
      (fun t => η t * inner ℝ (H10.value Ω hΩ v.val) (H10.value Ω hΩ (heatTrajectory S f t)))
      (η' t * inner ℝ (H10.value Ω hΩ v.val) (H10.value Ω hΩ (heatTrajectory S f t)) -
        η t * dirichletForm Ω hΩ v.val (heatTrajectory S f t)) t := by
    have hh := (hη t).smul (hmass t)
    convert! hh using 1
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hprod t)
    (((hη'.mul hm).sub (hηc.mul hb)).intervalIntegrable (μ := volume) 0 T)
  have hi₁ : IntervalIntegrable (fun t => η' t * inner ℝ (H10.value Ω hΩ v.val)
      (H10.value Ω hΩ (heatTrajectory S f t))) volume 0 T := (hη'.mul hm).intervalIntegrable 0 T
  have hi₂ : IntervalIntegrable (fun t => η t * dirichletForm Ω hΩ v.val
      (heatTrajectory S f t)) volume 0 T := (hηc.mul hb).intervalIntegrable 0 T
  rw [intervalIntegral.integral_sub hi₁ hi₂, hηT, zero_mul, zero_sub] at hi
  have hinit : inner ℝ (H10.value Ω hΩ v.val) (H10.value Ω hΩ (heatTrajectory S f 0)) =
      inner ℝ f (H10.value Ω hΩ v.val) := by
    rw [real_inner_comm]
    change inner ℝ (trialValue S (heatGalerkinFromL2 S f 0)) (trialValue S v) = _
    rw [heatGalerkinFromL2_zero]
    exact massProjection_spec (V := S) (trialValue S) (trialValue_injective S) f v
  rw [hinit] at hi
  simpa only [neg_mul] using hi
end PDE
