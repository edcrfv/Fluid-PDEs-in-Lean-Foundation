import PDE.AbsoluteContinuity
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Energy uniqueness through a time primitive

Lebesgue differentiation gives the a.e. derivative of a Bochner primitive. Its squared
physical norm is absolutely continuous. If its energy production is nonpositive, that
norm cannot grow from zero. Injectivity of the physical embedding forces the primitive
to vanish, and differentiation then forces the original L² trajectory to vanish a.e.
-/

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology
namespace PDE
variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Nonpositive physical energy production for a zero-initial primitive forces its derivative
trajectory to vanish. This supplies an energy uniqueness argument without assuming an L² trace. -/
theorem timeL2_eq_zero_of_primitive_energy {T : ℝ} (hT : 0 ≤ T) (u : TimeL2 V 0 T)
    (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (he : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      inner ℝ (J (∫ s in (0 : ℝ)..t, u s)) (J (u t)) ≤ 0) : u = 0 := by
  let P : ℝ → V := fun t => ∫ s in (0 : ℝ)..t, u s
  let e : ℝ → ℝ := fun t => ‖J (P t)‖ ^ 2
  have huI : IntegrableOn (fun t => u t) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT, IntegrableOn] using! (Lp.memLp u).integrable (by norm_num)
  have huInt := huI.intervalIntegrable
  have hpAC : AbsolutelyContinuousOnInterval P 0 T := intervalIntegral_absolutelyContinuous huInt
  have heAC : AbsolutelyContinuousOnInterval e 0 T :=
    absolutelyContinuous_norm_sq (absolutelyContinuous_clm J hpAC)
  have hpD := huInt.ae_hasDerivAt_integral
  have heVol : ∀ᵐ t ∂volume, t ∈ Icc (0 : ℝ) T → inner ℝ (J (P t)) (J (u t)) ≤ 0 :=
    (ae_restrict_iff' measurableSet_Icc).mp he
  have heD : ∀ᵐ t ∂volume, t ∈ Icc (0 : ℝ) T → deriv e t ≤ 0 := by
    filter_upwards [hpD, heVol] with t ht he' htmem
    have hdP : HasDerivAt P (u t) t := ht (by simpa only [uIcc_of_le hT] using htmem) 0 left_mem_uIcc
    have hd := (J.hasFDerivAt.comp_hasDerivAt t hdP).norm_sq
    change HasDerivAt e (2 * inner ℝ (J (P t)) (J (u t))) t at hd
    rw [hd.deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (he' htmem)
  have hanti := antitoneOn_of_absolutelyContinuous_of_deriv_nonpos hT heAC heD
  have hpzero (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : P t = 0 := by
    have hb := hanti ⟨le_rfl, hT⟩ ht ht.1
    have he0 : e 0 = 0 := by simp [e, P]
    rw [he0] at hb
    change ‖J (P t)‖ ^ 2 ≤ 0 at hb
    have hz : J (P t) = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (J (P t))])
    apply hJ
    simpa only [map_zero] using hz
  have hz : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) T), u t = 0 := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hpD] with t ht htmem
    have hdP : HasDerivAt P (u t) t := ht
      (by simpa only [uIcc_of_le hT] using ⟨htmem.1.le, htmem.2.le⟩) 0 left_mem_uIcc
    have hloc : P =ᶠ[𝓝 t] (fun _ => 0) := by
      filter_upwards [Ioo_mem_nhds htmem.1 htmem.2] with s hs
      exact hpzero s ⟨hs.1.le, hs.2.le⟩
    exact hdP.unique ((hasDerivAt_const t (0 : V)).congr_of_eventuallyEq hloc)
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hz
  exact Lp.ext (Filter.EventuallyEq.trans hz (Lp.coeFn_zero V 2 (volume.restrict (Icc (0 : ℝ) T))).symm)
end PDE
