import PDE.DistributionalInterval
import PDE.CountableTesting
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Simultaneous weak testing on almost every interval slice

Fubini initially gives a null exceptional set for each compact smooth test.
This file proves the needed exchange of quantifiers using a countable dense
subset of the test graph in L² × L² and continuity of the actual residual.
No countability of the smooth-test class is assumed.
-/

open MeasureTheory Set InnerProductSpace
open scoped ContDiff ENNReal

namespace PDE

private abbrev IntervalTest (a b : ℝ) :=
  {φ : ℝ → ℝ // ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo a b}

private noncomputable def intervalTestGraph {a b : ℝ} (φ : IntervalTest a b) :
    TimeL2 ℝ a b × TimeL2 ℝ a b :=
  ((φ.property.1.continuous.memLp_of_hasCompactSupport φ.property.2.1).toLp φ.val,
    ((φ.property.1.continuous_deriv (by simp)).memLp_of_hasCompactSupport
      φ.property.2.1.deriv).toLp (deriv φ.val))

private noncomputable def intervalSliceResidual (a b : ℝ) (u du : ℝ → ℝ) :
    (TimeL2 ℝ a b × TimeL2 ℝ a b) →L[ℝ] ℝ := by
  classical
  exact if h : MemLp u 2 (volume.restrict (Icc a b)) ∧ MemLp du 2 (volume.restrict (Icc a b)) then
    (innerSL ℝ (h.1.toLp u)).comp (ContinuousLinearMap.snd ℝ _ _) +
      (innerSL ℝ (h.2.toLp du)).comp (ContinuousLinearMap.fst ℝ _ _)
  else 0

private theorem intervalSliceResidual_test {a b : ℝ} {u du : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Icc a b)))
    (hd : MemLp du 2 (volume.restrict (Icc a b))) (φ : IntervalTest a b) :
    intervalSliceResidual a b u du (intervalTestGraph φ) =
      (∫ t in Icc a b, deriv φ.val t * u t) + ∫ t in Icc a b, φ.val t * du t := by
  rw [intervalSliceResidual, dite_eq_left ⟨hu, hd⟩]
  change inner ℝ (hu.toLp u) (intervalTestGraph φ).2 +
    inner ℝ (hd.toLp du) (intervalTestGraph φ).1 = _
  rw [L2.inner_def, L2.inner_def]
  congr 1
  · apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp,
      ((φ.property.1.continuous_deriv (by simp)).memLp_of_hasCompactSupport
        φ.property.2.1.deriv : MemLp (deriv φ.val) 2 (volume.restrict (Icc a b))).coeFn_toLp]
      with t hut hφt
    simp [intervalTestGraph, hut, hφt, mul_comm]
  · apply integral_congr_ae
    filter_upwards [hd.coeFn_toLp,
      (φ.property.1.continuous.memLp_of_hasCompactSupport φ.property.2.1 :
        MemLp φ.val 2 (volume.restrict (Icc a b))).coeFn_toLp] with t hdt hφt
    simp [intervalTestGraph, hdt, hφt, mul_comm]

/-- Per-test a.e. identities imply genuine distributional differentiation on
almost every slice, with one common full-measure set for all compact tests. -/
theorem ae_hasWeakDerivativeOnInterval_of_test_identities
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b : ℝ} {u du : α → ℝ → ℝ}
    (hslices : ∀ᵐ x ∂μ, MemLp (u x) 2 (volume.restrict (Icc a b)) ∧
      MemLp (du x) 2 (volume.restrict (Icc a b)))
    (htest : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      ∀ᵐ x ∂μ, (∫ t in Icc a b, deriv φ t * u x t) = -(∫ t in Icc a b, φ t * du x t)) :
    ∀ᵐ x ∂μ, HasWeakDerivativeOnInterval a b (u x) (du x) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  have hzero : ∀ φ : IntervalTest a b, ∀ᵐ x ∂μ,
      intervalSliceResidual a b (u x) (du x) (intervalTestGraph φ) = 0 := by
    intro φ
    filter_upwards [hslices, htest φ.val φ.property.1 φ.property.2.1 φ.property.2.2]
      with x hx ht
    rw [intervalSliceResidual_test hx.1 hx.2 φ, ht, neg_add_cancel]
  have hall := ae_forall_continuous_tests (intervalTestGraph (a := a) (b := b))
    (fun x => intervalSliceResidual a b (u x) (du x))
    (Filter.Eventually.of_forall fun x => (intervalSliceResidual a b (u x) (du x)).continuous) hzero
  filter_upwards [hslices, hall] with x hx hxall
  refine ⟨hx.1.integrable (by norm_num), hx.2.integrable (by norm_num), ?_⟩
  intro φ hφ hc hs
  have ht := hxall ⟨φ, hφ, hc, hs⟩
  rw [intervalSliceResidual_test hx.1 hx.2] at ht
  exact eq_neg_of_add_eq_zero_left ht

/-- The common set of valid weak slices supplies AC representatives and their
actual derivatives; it does not assert a single pointwise representative on a cylinder. -/
theorem ae_exists_interval_AC_representative_of_test_identities
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b : ℝ} (hab : a < b)
    {u du : α → ℝ → ℝ}
    (hslices : ∀ᵐ x ∂μ, MemLp (u x) 2 (volume.restrict (Icc a b)) ∧
      MemLp (du x) 2 (volume.restrict (Icc a b)))
    (htest : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      ∀ᵐ x ∂μ, (∫ t in Icc a b, deriv φ t * u x t) = -(∫ t in Icc a b, φ t * du x t)) :
    ∀ᵐ x ∂μ, ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v a b ∧
      u x =ᵐ[volume.restrict (Icc a b)] v ∧ deriv v =ᵐ[volume.restrict (Icc a b)] du x :=
  (ae_hasWeakDerivativeOnInterval_of_test_identities hslices htest).mono
    fun _ hx => hx.exists_absolutelyContinuous_representative hab

end PDE
