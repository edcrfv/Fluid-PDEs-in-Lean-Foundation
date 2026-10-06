import PDE.SobolevSlicing
import PDE.ClassicalWeakDerivative
import PDE.IntervalWeakChainRule
import PDE.IntervalWeakBound

/-! A nonzero-boundary affine weak function with a changed interior point.
This checks that reconstruction produces an a.e. representative, and does
not incorrectly conclude regularity of the originally supplied values. -/

open PDE MeasureTheory Set

private def affineInterval (x : Space 1) : ℝ := 7 + x 0

private theorem affineInterval_deriv (x : Space 1) : coordDeriv 0 affineInterval x = 1 := by
  have h := coordDeriv_interval_test (φ := fun t : ℝ => 7 + t) (by fun_prop) x
  change coordDeriv 0 (fun y : Space 1 => 7 + y 0) x = 1
  simpa using h

private theorem affineInterval_memLp :
    MemLp affineInterval 2 (volume.restrict (intervalDomain 0 1)) := by
  have hc : Continuous affineInterval := by unfold affineInterval; fun_prop
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  apply ((hc.pow 2).continuousOn.integrableOn_compact
    (isCompact_Icc : IsCompact (Icc (fun _ : Fin 1 => (0 : ℝ)) (fun _ => 1)))).mono_set
  intro x hx
  constructor <;> intro i <;> have hi : i = 0 := Subsingleton.elim _ _
  · simpa [hi] using hx.1.le
  · simpa [hi] using hx.2.le

private theorem affineWeak : HasWeakDerivativeOnInterval 0 1 (fun t => 7 + t) (fun _ => 1) := by
  let : IsFiniteMeasure (volume.restrict (intervalDomain 0 1)) := by
    rw [← (intervalLift_measurePreserving 0 1).map_eq]
    exact Measure.isFiniteMeasure_map _ _
  have hw := hasWeakPartialOn_of_contDiffOn (isOpen_intervalDomain 0 1) 0
    (u := affineInterval) (by unfold affineInterval; fun_prop)
  have he : coordDeriv 0 affineInterval = fun _ => 1 := funext affineInterval_deriv
  rw [he] at hw
  exact hw.to_interval affineInterval_memLp (memLp_const 1)

-- Altering a single interior point does not change a distributional derivative.
private noncomputable def alteredAffine (t : ℝ) : ℝ := if t = 1 / 2 then 1000 else 7 + t

private theorem alteredAffine_ae :
    (fun t : ℝ => 7 + t) =ᵐ[volume.restrict (Icc 0 1)] alteredAffine := by
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 / 2 := by simp [ae_iff]
  filter_upwards [ae_restrict_of_ae hne] with t ht
  simp only [alteredAffine, ite_eq_right ht]

example : ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v 0 1 ∧
    alteredAffine =ᵐ[volume.restrict (Icc 0 1)] v ∧
    deriv v =ᵐ[volume.restrict (Icc 0 1)] fun _ => 1 :=
  (affineWeak.congr alteredAffine_ae Filter.EventuallyEq.rfl).exists_absolutelyContinuous_representative
    (by norm_num)

example : alteredAffine (1 / 2) ≠ 7 + (1 / 2 : ℝ) := by norm_num [alteredAffine]

-- The mean estimate is unchanged by the exceptional point and does not
-- require the nonzero boundary values 7 and 8 to vanish.
example : (∫ t in Icc 0 1, (alteredAffine t - ∫ s in Icc 0 1, alteredAffine s) ^ 2) ≤ 1 := by
  have hf := affineInterval_memLp.comp_measurePreserving (intervalLift_measurePreserving 0 1)
  have ha : MemLp alteredAffine 2 (volume.restrict (Icc 0 1)) := hf.ae_eq alteredAffine_ae
  have h := (affineWeak.congr alteredAffine_ae Filter.EventuallyEq.rfl).mean_poincare
    (by norm_num) ha (memLp_const 1)
  norm_num at h ⊢
  exact h

-- A globally non-Lipschitz C¹ outer function still has the genuine weak chain
-- rule on the interval. The input representative retains its exceptional point.
example : HasWeakDerivativeOnInterval 0 1 (fun t => alteredAffine t ^ 2)
    (fun t => 2 * alteredAffine t) := by
  have h := (affineWeak.congr alteredAffine_ae Filter.EventuallyEq.rfl).comp_contDiff
    (by norm_num) (Φ := fun x => x ^ 2) (by fun_prop)
  simpa using h

-- The weak supremum estimate is an a.e. bound, despite the value 1000 at 1/2.
example : ∀ᵐ t ∂unitIntervalMeasure, |alteredAffine t| ≤ 9 := by
  have hw := affineWeak.congr alteredAffine_ae Filter.EventuallyEq.rfl
  have hi : (∫ s, |alteredAffine s| ∂unitIntervalMeasure) ≤ 8 := by
    have hm : ∀ᵐ s ∂unitIntervalMeasure, |alteredAffine s| ≤ 8 := by
      filter_upwards [alteredAffine_ae, ae_restrict_mem measurableSet_Icc] with s hs hmem
      rw [← hs, abs_of_nonneg (by linarith [hmem.1])]
      linarith [hmem.2]
    have hai : Integrable (fun s => |alteredAffine s|) unitIntervalMeasure := hw.integrable.abs
    have h := integral_mono_ae hai (integrable_const (8 : ℝ)) hm
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h
  filter_upwards [hw.ae_abs_le_integral_abs] with t ht
  norm_num only [abs_one, integral_const, probReal_univ, smul_eq_mul, one_mul] at ht
  linarith

example : ¬ ∀ t ∈ Icc (0 : ℝ) 1, |alteredAffine t| ≤ 9 := by
  intro h
  have ht := h (1 / 2) (by norm_num)
  norm_num [alteredAffine] at ht
