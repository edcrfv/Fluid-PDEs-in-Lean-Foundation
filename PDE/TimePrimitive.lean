import PDE.TimeIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Continuous representatives from an integrated time equation

The prescribed initial value plus the Bochner integral of the derivative is continuous
on the time interval and satisfies the integrated equation. Fubini proves integration
by parts without assuming a classical derivative of the primitive. Compact smooth test
separation identifies this representative with every L² trajectory satisfying that equation.
-/

open MeasureTheory Set
open scoped ContDiff
namespace PDE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Reconstruct a representative from the prescribed initial value and time derivative. -/
noncomputable def timePrimitive (a : ℝ) (c : E) (du : ℝ → E) (t : ℝ) : E :=
  c + ∫ s in Icc a t, du s

omit [CompleteSpace E] in
theorem timePrimitive_initial (a : ℝ) (c : E) (du : ℝ → E) : timePrimitive a c du a = c := by
  simp [timePrimitive]

omit [CompleteSpace E] in
theorem timePrimitive_continuousOn {a b : ℝ} (c : E) {du : ℝ → E}
    (hdu : IntegrableOn du (Icc a b)) : ContinuousOn (timePrimitive a c du) (Icc a b) :=
  continuousOn_const.add (intervalIntegral.continuousOn_primitive_Icc hdu)

/-- A primitive satisfies the time-integrated equation with its prescribed initial value. -/
theorem timePrimitive_integrated {a b : ℝ} (hab : a ≤ b) (c : E) {du : ℝ → E}
    (hdu : IntegrableOn du (Icc a b)) (η η' : ℝ → ℝ)
    (hη : ∀ t, HasDerivAt η (η' t) t) (hη' : Continuous η') (hηb : η b = 0) :
    (∫ t in Icc a b, η' t • timePrimitive a c du t) +
      (∫ t in Icc a b, η t • du t) = (-η a) • c := by
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun t => (hη t).continuousAt
  have hfuture (s : ℝ) (hs : s ∈ Icc a b) : (∫ t in Icc s b, η' t) = -η s := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hη t)
      (hη'.intervalIntegrable (μ := volume) s b)
    rwa [intervalIntegral.integral_of_le hs.2, ← integral_Icc_eq_integral_Ioc, hηb, zero_sub] at h
  have hpast : (∫ t in Icc a b, η' t • (∫ s in Icc a t, du s)) =
      -(∫ t in Icc a b, η t • du t) := by
    rw [integral_past_smul_eq_future_smul hη'.integrableOn_Icc hdu, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    change (∫ t in Icc s b, η' t) • du s = -(η s • du s)
    rw [hfuture s hs, neg_smul]
  have hconst : (∫ t in Icc a b, η' t • c) = (-η a) • c := by
    rw [integral_smul_const, hfuture a ⟨le_rfl, hab⟩]
  have hpcont := intervalIntegral.continuousOn_primitive_Icc hdu
  have hpc : IntegrableOn (fun t => η' t • (∫ s in Icc a t, du s)) (Icc a b) :=
    (hη'.continuousOn.smul hpcont).integrableOn_compact isCompact_Icc
  have hcc : IntegrableOn (fun t => η' t • c) (Icc a b) :=
    (hη'.smul continuous_const).integrableOn_Icc
  simp_rw [timePrimitive, smul_add]
  rw [integral_add hcc hpc, hconst, hpast]
  abel

/-- An integrated Bochner equation with an initial datum identifies the continuous primitive
as an a.e. representative, not merely as a formal candidate. -/
theorem ae_eq_timePrimitive_of_integrated {a b : ℝ} (hab : a ≤ b) (c : E)
    (u du : TimeL2 E a b)
    (hu : ∀ (η η' : ℝ → ℝ), (∀ t, HasDerivAt η (η' t) t) → Continuous η' → η b = 0 →
      (∫ t in Icc a b, η' t • u t) + (∫ t in Icc a b, η t • du t) = (-η a) • c) :
    u =ᵐ[volume.restrict (Icc a b)] timePrimitive a c du := by
  have hdu : IntegrableOn (fun t => du t) (Icc a b) := (Lp.memLp du).integrable (by norm_num)
  have hpc := timePrimitive_continuousOn c hdu
  have hpi : IntegrableOn (timePrimitive a c du) (Icc a b) :=
    hpc.integrableOn_compact isCompact_Icc
  have hdiff : IntegrableOn (fun t => u t - timePrimitive a c du t) (Icc a b) :=
    ((Lp.memLp u).integrable (by norm_num)).sub hpi
  have hz : ∀ᵐ t ∂volume, t ∈ Ioo a b → u t - timePrimitive a c du t = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hdiff.mono_set Ioo_subset_Icc_self).locallyIntegrableOn)
    intro φ hφ hc hs
    let η : ℝ → ℝ := fun t => ∫ s in b..t, φ s
    have hη : ∀ t, HasDerivAt η (φ t) t := by
      intro t
      exact intervalIntegral.integral_hasDerivAt_right (hφ.continuous.intervalIntegrable b t)
        (hφ.continuous.stronglyMeasurableAtFilter volume (nhds t)) hφ.continuous.continuousAt
    have hηb : η b = 0 := by simp [η]
    have h₁ := hu η φ hη hφ.continuous hηb
    have h₂ := timePrimitive_integrated hab c hdu η φ hη hφ.continuous hηb
    have hpair : (∫ t in Icc a b, φ t • (u t - timePrimitive a c du t)) = 0 := by
      simp_rw [smul_sub]
      have hφp : IntegrableOn (fun t => φ t • timePrimitive a c du t) (Icc a b) :=
        (hφ.continuous.continuousOn.smul hpc).integrableOn_compact isCompact_Icc
      rw [integral_sub (timeL2_weighted_integrable u φ hφ.continuous) hφp]
      exact sub_eq_zero.mpr (add_right_cancel (h₁.trans h₂.symm))
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc a b)]
    · exact hpair
    · intro t ht
      have hφt : φ t = 0 := image_eq_zero_of_notMem_tsupport
        (fun hm => ht (Ioo_subset_Icc_self (hs hm)))
      rw [hφt, zero_smul]
  have he : ∀ᵐ t ∂volume.restrict (Ioo a b), u t = timePrimitive a c du t := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hz] with t ht hm
    exact sub_eq_zero.mp (ht hm)
  rwa [Measure.restrict_congr_set Ioo_ae_eq_Icc] at he
end PDE
