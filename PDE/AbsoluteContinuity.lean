import PDE.TimePrimitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Absolute continuity and energy tests

Increment bounds transfer absolute continuity. Comparing a Bochner primitive with the
scalar primitive of its norm proves absolute continuity in a normed space. Bounded linear
maps, norms and squared norms preserve it on finite intervals. The scalar fundamental
theorem then turns an a.e. derivative sign into monotonicity.
-/

open MeasureTheory Set Filter
open scoped Topology
namespace PDE

/-- Absolute continuity transfers across pointwise control of increments on the interval. -/
theorem absolutelyContinuousOnInterval_of_dist_le {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {a b : ℝ} {f : ℝ → X} {g : ℝ → Y}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hf : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, dist (f x) (f y) ≤ dist (g x) (g y)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, hgδ⟩ := hg ε hε
  refine ⟨δ, hδ, fun I hI hlen => ?_⟩
  apply lt_of_le_of_lt _ (hgδ I hI hlen)
  apply Finset.sum_le_sum
  intro i hi
  have hm := (mem_ofPred_eq.mp hI).1 i hi
  exact hf _ hm.1 _ hm.2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Bochner primitives are absolutely continuous, by comparison with the scalar norm primitive. -/
theorem intervalIntegral_absolutelyContinuous {f : ℝ → E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    AbsolutelyContinuousOnInterval (fun t => ∫ s in a..t, f s) a b := by
  have hnorm := hf.norm.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  apply absolutelyContinuousOnInterval_of_dist_le hnorm
  intro x hx y hy
  have hax : IntervalIntegrable f volume a x := hf.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc left_mem_uIcc hx))
  have hay : IntervalIntegrable f volume a y := hf.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc left_mem_uIcc hy))
  rw [dist_eq_norm, Real.dist_eq, intervalIntegral.integral_interval_sub_left hax hay,
    intervalIntegral.integral_interval_sub_left hax.norm hay.norm]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

omit [NormedSpace ℝ E] in
/-- The norm of an absolutely continuous Banach-valued curve is absolutely continuous. -/
theorem absolutelyContinuous_norm {f : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => ‖f t‖) a b :=
  absolutelyContinuousOnInterval_of_dist_le hf (fun x _ y _ => by simpa only [dist_eq_norm] using dist_norm_norm_le (f x) (f y))

/-- Bounded linear maps preserve absolute continuity. -/
theorem absolutelyContinuous_clm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {f : ℝ → E} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => L (f t)) a b := by
  apply absolutelyContinuousOnInterval_of_dist_le (hf.const_smul ‖L‖)
  intro x _ y _
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg L)]
  exact L.lipschitzWith.dist_le_mul _ _

omit [NormedSpace ℝ E] in
/-- Squared norms of absolutely continuous curves are absolutely continuous on a finite interval. -/
theorem absolutelyContinuous_norm_sq {f : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => ‖f t‖ ^ 2) a b := by
  have hn := absolutelyContinuous_norm hf
  simpa only [Pi.mul_apply, pow_two] using! hn.mul hn

/-- The a.e. sign of the derivative controls an absolutely continuous scalar function. -/
theorem antitoneOn_of_absolutelyContinuous_of_deriv_nonpos {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ t ∂volume, t ∈ Icc a b → deriv f t ≤ 0) : AntitoneOn f (Icc a b) := by
  intro x hx y hy hxy
  have hsub : uIcc x y ⊆ uIcc a b := uIcc_subset_uIcc
    (by simpa only [uIcc_of_le hab] using hx) (by simpa only [uIcc_of_le hab] using hy)
  have he := (hf.mono hsub).integral_deriv_eq_sub
  have hn : (∫ t in x..y, deriv f t) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hxy]
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hd] with t ht hd'
    exact hd' ⟨hx.1.trans ht.1.le, ht.2.trans hy.2⟩
  linarith
end PDE
