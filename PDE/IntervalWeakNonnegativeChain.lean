import PDE.IntervalWeakPositivePart

/-! Chain rules on the nonnegative range of a weak function. A nonnegative
AC representative is constructed, rather than assuming positivity pointwise
for an arbitrary representative or extending a singular scalar map to ℝ. -/

open MeasureTheory Set
open scoped NNReal

namespace PDE

theorem HasWeakDerivativeOnInterval.exists_nonneg_absolutelyContinuous_representative
    {a b : ℝ} (hab : a < b) {u du : ℝ → ℝ}
    (hu : HasWeakDerivativeOnInterval a b u du)
    (hn : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ u t) :
    ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v a b ∧ (∀ t, 0 ≤ v t) ∧
      u =ᵐ[volume.restrict (Icc a b)] v ∧
      deriv v =ᵐ[volume.restrict (Icc a b)] du := by
  obtain ⟨v, hv, huv, hdv⟩ := hu.exists_absolutelyContinuous_representative hab
  refine ⟨fun t => max (v t) 0, absolutelyContinuous_positivePart hv,
    fun _ => le_max_right _ _, ?_, ?_⟩
  · filter_upwards [huv, hn] with t ht hnt
    rw [← ht, max_eq_left hnt]
  · filter_upwards [ae_restrict_of_ae hv.ae_differentiableAt,
      ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (ae_deriv_eq_zero_on_level v 0),
      huv, hdv, hn] with t ht hm hk hut hdt hnt
    have hvd := ht (by simpa only [uIcc_of_le hab.le] using hm)
    rw [(hasDerivAt_positivePart hvd.hasDerivAt hk).deriv]
    by_cases hp : 0 < v t
    · simpa only [ite_eq_left hp] using hdt
    · have hz : v t = 0 := le_antisymm (le_of_not_gt hp) (hut ▸ hnt)
      simp only [ite_eq_right hp, ← hdt, hk hz]

/-- A scalar map that is Lipschitz and differentiable on the nonnegative
half-line can be composed with a nonnegative weak interval function. -/
theorem HasWeakDerivativeOnInterval.comp_nonneg {a b : ℝ} (hab : a < b)
    {u du Φ D : ℝ → ℝ} {K : ℝ≥0}
    (hu : HasWeakDerivativeOnInterval a b u du)
    (hn : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ u t)
    (hL : LipschitzOnWith K Φ (Ici 0))
    (hD : ∀ x, 0 ≤ x → HasDerivAt Φ (D x) x) :
    HasWeakDerivativeOnInterval a b (fun t => Φ (u t))
      (fun t => D (u t) * du t) := by
  obtain ⟨v, hv, hvn, huv, hdv⟩ :=
    hu.exists_nonneg_absolutelyContinuous_representative hab hn
  have hc : AbsolutelyContinuousOnInterval (fun t => Φ (v t)) a b := by
    apply absolutelyContinuousOnInterval_of_dist_le (hv.const_mul (K : ℝ))
    intro x _ y _
    simpa only [Pi.smul_apply, smul_eq_mul, dist_eq_norm, ← mul_sub, norm_mul,
      Real.norm_of_nonneg K.coe_nonneg] using hL.dist_le_mul (v x) (hvn x) (v y) (hvn y)
  apply (hasWeakDerivativeOnInterval_of_absolutelyContinuous hab hc).congr
    (huv.symm.mono fun _ ht => congrArg Φ ht)
  filter_upwards [ae_restrict_of_ae hv.ae_differentiableAt,
    ae_restrict_mem measurableSet_Icc, huv, hdv] with t ht hm hut hdt
  have hvd := ht (by simpa only [uIcc_of_le hab.le] using hm)
  have he := ((hD (v t) (hvn t)).comp t hvd.hasDerivAt).deriv
  simpa only [Function.comp_def, ← hut, hdt] using he

end PDE
