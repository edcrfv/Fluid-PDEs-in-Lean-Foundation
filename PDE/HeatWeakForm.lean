import PDE.HeatBochner
import PDE.TimePairing

/-!
# Time-integrated heat formulation

Continuous time tests define L² classes. The mass and stiffness tests give a bounded
linear residual in the spatial test, with an explicit time-integral formula including
the original L² initial datum. Initial traces and continuity in L² require further results.
-/

open InnerProductSpace MeasureTheory Set Filter
open scoped Topology ENNReal
namespace PDE
variable {n : ℕ} {Ω : Set (Space n)} {hΩ : IsOpen Ω}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] trialNormedAddCommGroup trialSeminormedAddCommGroup
  trialNormedSpace trialInnerProductSpace trialDualTopology

theorem continuous_time_memLp (g : ℝ → ℝ) (hg : Continuous g) (T : ℝ) :
    MemLp g 2 (volume.restrict (Icc (0 : ℝ) T)) :=
  (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr ((hg.pow 2).integrableOn_Icc)

noncomputable def continuousTimeL2 (g : ℝ → ℝ) (hg : Continuous g) (T : ℝ) :
    Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)) := (continuous_time_memLp g hg T).toLp g

theorem continuousTimeL2_ae (g : ℝ → ℝ) (hg : Continuous g) (T : ℝ) :
    continuousTimeL2 g hg T =ᵐ[volume.restrict (Icc (0 : ℝ) T)] g := MemLp.coeFn_toLp _

noncomputable def heatMassForm (Ω : Set (Space n)) (hΩ : IsOpen Ω) :
    H10 Ω hΩ →L[ℝ] H10 Ω hΩ →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (H10.value Ω hΩ) (H10.value Ω hΩ)

theorem heatMassForm_apply (u v : H10 Ω hΩ) :
    heatMassForm Ω hΩ u v = inner ℝ (H10.value Ω hΩ u) (H10.value Ω hΩ v) := rfl

noncomputable def heatTimeResidual (f : DomainL2 Ω) (T : ℝ) (u : HeatEnergySpace Ω hΩ T)
    (η η' : ℝ → ℝ) (hη : Continuous η) (hη' : Continuous η') : H10 Ω hΩ →L[ℝ] ℝ :=
  (weightedTimeForm (V := H10 Ω hΩ) (continuousTimeL2 η' hη' T) (heatMassForm Ω hΩ)).flip u -
    (weightedTimeForm (V := H10 Ω hΩ) (continuousTimeL2 η hη T) (dirichletForm Ω hΩ)).flip u +
      η 0 • poissonLoad Ω hΩ f

theorem heatTimeResidual_apply (f : DomainL2 Ω) (T : ℝ) (u : HeatEnergySpace Ω hΩ T)
    (η η' : ℝ → ℝ) (hη : Continuous η) (hη' : Continuous η') (v : H10 Ω hΩ) :
    heatTimeResidual f T u η η' hη hη' v =
      (∫ t in Icc (0 : ℝ) T, η' t * inner ℝ (H10.value Ω hΩ v) (H10.value Ω hΩ (u t))) -
      (∫ t in Icc (0 : ℝ) T, η t * dirichletForm Ω hΩ v (u t)) +
        η 0 * inner ℝ f (H10.value Ω hΩ v) := by
  change weightedTimeForm (V := H10 Ω hΩ) _ _ v u - weightedTimeForm (V := H10 Ω hΩ) _ _ v u + _ = _
  rw [weightedTimeForm_apply, weightedTimeForm_apply]
  congr 2
  · apply integral_congr_ae
    filter_upwards [continuousTimeL2_ae η' hη' T] with t ht
    rw [ht, heatMassForm_apply]
  · apply integral_congr_ae
    filter_upwards [continuousTimeL2_ae η hη T] with t ht
    rw [ht]

/-- An energy-space heat equation with the initial datum in its time-integrated formulation.
This definition does not yet assert a continuous-in-L² representative or a pointwise trace. -/
def IsIntegratedWeakHeatSolution (f : DomainL2 Ω) (T : ℝ) (u : HeatEnergySpace Ω hΩ T) : Prop :=
  ∀ (η η' : ℝ → ℝ), (∀ t, HasDerivAt η (η' t) t) → Continuous η' → η T = 0 →
    ∀ v : H10 Ω hΩ,
      (∫ t in Icc (0 : ℝ) T, η' t * inner ℝ (H10.value Ω hΩ v) (H10.value Ω hΩ (u t))) -
      (∫ t in Icc (0 : ℝ) T, η t * dirichletForm Ω hΩ v (u t)) =
        -η 0 * inner ℝ f (H10.value Ω hΩ v)

theorem heatTimeIntegrands_integrable (T : ℝ) (u : HeatEnergySpace Ω hΩ T)
    (g : ℝ → ℝ) (hg : Continuous g) (v : H10 Ω hΩ) :
    IntegrableOn (fun t => g t * inner ℝ (H10.value Ω hΩ v) (H10.value Ω hΩ (u t)))
      (Icc (0 : ℝ) T) ∧
    IntegrableOn (fun t => g t * dirichletForm Ω hΩ v (u t)) (Icc (0 : ℝ) T) := by
  constructor
  · have hi := weightedTimeForm_integrable (V := H10 Ω hΩ) (continuousTimeL2 g hg T)
      (heatMassForm Ω hΩ) v u
    apply hi.congr
    filter_upwards [continuousTimeL2_ae g hg T] with t ht
    rw [ht, heatMassForm_apply]
  · have hi := weightedTimeForm_integrable (V := H10 Ω hΩ) (continuousTimeL2 g hg T)
      (dirichletForm Ω hΩ) v u
    apply hi.congr
    filter_upwards [continuousTimeL2_ae g hg T] with t ht
    rw [ht]

end PDE
