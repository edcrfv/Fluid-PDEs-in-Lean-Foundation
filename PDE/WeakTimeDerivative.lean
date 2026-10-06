import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Weak time derivatives in Bochner L²

Both the trajectory and derivative are a.e. classes on a finite interval in a complete
normed real space. Scalar C¹ tests vanishing at the endpoints express time integration
by parts. Hölder proves the Bochner integrability of these tests; compact smooth test
separation proves uniqueness of the derivative as an L² class.
-/

open MeasureTheory Set
open scoped ContDiff
namespace PDE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Bochner L² space on a real closed interval; endpoints have zero Lebesgue measure. -/
noncomputable abbrev TimeL2 (E : Type*) [NormedAddCommGroup E] (a b : ℝ) :=
  Lp E 2 (volume.restrict (Icc a b))

/-- Square-integrable weak time differentiation, tested against scalar C¹ functions
vanishing at both endpoints. Both entries are actual Bochner L² a.e. classes. -/
def HasL2TimeDerivative [CompleteSpace E] (a b : ℝ) (u du : TimeL2 E a b) : Prop :=
  ∀ (η η' : ℝ → ℝ), (∀ t, HasDerivAt η (η' t) t) → Continuous η' → η a = 0 → η b = 0 →
    (∫ t in Icc a b, η' t • u t) = -(∫ t in Icc a b, η t • du t)

/-- L² times L² is Bochner integrable by Hölder. -/
theorem timeL2_weighted_integrable {a b : ℝ} (u : TimeL2 E a b)
    (g : ℝ → ℝ) (hg : Continuous g) : IntegrableOn (fun t => g t • u t) (Icc a b) := by
  have hg2 : MemLp g 2 (volume.restrict (Icc a b)) :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr ((hg.pow 2).integrableOn_Icc)
  exact memLp_one_iff_integrable.mp ((Lp.memLp u).smul hg2)

variable [CompleteSpace E]

/-- The L² time derivative is unique as an a.e. class. -/
theorem HasL2TimeDerivative.unique {a b : ℝ} {u du dv : TimeL2 E a b}
    (hu : HasL2TimeDerivative a b u du) (hv : HasL2TimeDerivative a b u dv) : du = dv := by
  apply Lp.ext
  have hd : IntegrableOn (fun t => du t - dv t) (Icc a b) :=
    ((Lp.memLp du).integrable (by norm_num)).sub ((Lp.memLp dv).integrable (by norm_num))
  have hz : ∀ᵐ t ∂volume, t ∈ Ioo a b → du t - dv t = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hd.mono_set Ioo_subset_Icc_self).locallyIntegrableOn)
    intro φ hφ hc hs
    have ha : φ a = 0 := image_eq_zero_of_notMem_tsupport (fun ht => (hs ht).1.false)
    have hb : φ b = 0 := image_eq_zero_of_notMem_tsupport (fun ht => (hs ht).2.false)
    have hp : ∀ t, HasDerivAt φ (deriv φ t) t := fun t =>
      (hφ.differentiable (by simp)).differentiableAt.hasDerivAt
    have huφ := hu φ (deriv φ) hp (hφ.continuous_deriv (by simp)) ha hb
    have hvφ := hv φ (deriv φ) hp (hφ.continuous_deriv (by simp)) ha hb
    have he : (∫ t in Icc a b, φ t • du t) = ∫ t in Icc a b, φ t • dv t :=
      neg_injective (huφ.symm.trans hvφ)
    have hi : (∫ t in Icc a b, φ t • (du t - dv t)) = 0 := by
      simp_rw [smul_sub]
      rw [integral_sub (timeL2_weighted_integrable du φ hφ.continuous)
        (timeL2_weighted_integrable dv φ hφ.continuous), he, sub_self]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc a b)]
    · exact hi
    · intro t ht
      have hφt : φ t = 0 := image_eq_zero_of_notMem_tsupport
        (fun hm => ht (Ioo_subset_Icc_self (hs hm)))
      rw [hφt, zero_smul]
  have he : ∀ᵐ t ∂volume.restrict (Ioo a b), du t = dv t := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hz] with t ht hmem
    exact sub_eq_zero.mp (ht hmem)
  rwa [Measure.restrict_congr_set Ioo_ae_eq_Icc] at he
end PDE
