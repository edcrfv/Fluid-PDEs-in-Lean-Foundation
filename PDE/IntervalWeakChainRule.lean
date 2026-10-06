import PDE.DistributionalInterval

/-! C¹ composition for genuine interval distributional derivatives.
The rule is obtained from the reconstructed AC representative. No positivity,
pointwise regularity of the original representative, or boundary trace is assumed. -/

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace PDE

/-- A C¹ scalar composition preserves absolute continuity on a compact interval;
only a Lipschitz bound on the compact range is needed, and it is derived. -/
theorem absolutelyContinuous_comp_contDiff {a b : ℝ} {v Φ : ℝ → ℝ}
    (hv : AbsolutelyContinuousOnInterval v a b) (hΦ : ContDiff ℝ 1 Φ) :
    AbsolutelyContinuousOnInterval (fun t => Φ (v t)) a b := by
  obtain ⟨C, hC⟩ := hv.exists_bound
  have hr (t : ℝ) (ht : t ∈ uIcc a b) : v t ∈ Icc (-C) C := by
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hC t ht)
  obtain ⟨K, hK⟩ := hΦ.contDiffOn.exists_lipschitzOnWith
    (by decide) (convex_Icc (-C) C) isCompact_Icc
  apply absolutelyContinuousOnInterval_of_dist_le (hv.const_mul (K : ℝ))
  intro x hx y hy
  simpa only [Pi.smul_apply, smul_eq_mul, dist_eq_norm, ← mul_sub, norm_mul,
    Real.norm_of_nonneg K.coe_nonneg] using hK.dist_le_mul (v x) (hr x hx) (v y) (hr y hy)

/-- An AC scalar curve satisfies the compact smooth distributional identity
with its actual a.e. derivative. The function's endpoint values are unrestricted. -/
theorem hasWeakDerivativeOnInterval_of_absolutelyContinuous {a b : ℝ} (hab : a < b)
    {v : ℝ → ℝ} (hv : AbsolutelyContinuousOnInterval v a b) :
    HasWeakDerivativeOnInterval a b v (deriv v) := by
  have hvcont : ContinuousOn v (Icc a b) := by simpa [uIcc_of_le hab.le] using hv.continuousOn
  refine ⟨hvcont.integrableOn_Icc,
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp hv.intervalIntegrable_deriv, ?_⟩
  intro φ hφ _hc hs
  have hφac := (hφ.of_le (by simp : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).contDiffOn.absolutelyContinuousOnInterval
    (a := a) (b := b)
  have ha : φ a = 0 := image_eq_zero_of_notMem_tsupport (fun ht => (hs ht).1.false)
  have hb : φ b = 0 := image_eq_zero_of_notMem_tsupport (fun ht => (hs ht).2.false)
  have h := hv.integral_mul_deriv_eq_deriv_mul hφac
  simpa only [ha, hb, mul_zero, sub_self, zero_sub, intervalIntegral.integral_of_le hab.le,
    ← integral_Icc_eq_integral_Ioc, smul_eq_mul, mul_comm] using h

/-- The chain rule follows from the actual compact-test weak derivative.
It also proves integrability of the composed value and derivative. -/
theorem HasWeakDerivativeOnInterval.comp_contDiff {a b : ℝ} (hab : a < b)
    {u du Φ : ℝ → ℝ} (hu : HasWeakDerivativeOnInterval a b u du)
    (hΦ : ContDiff ℝ 1 Φ) :
    HasWeakDerivativeOnInterval a b (fun t => Φ (u t))
      (fun t => deriv Φ (u t) * du t) := by
  obtain ⟨v, hv, huv, hdv⟩ := hu.exists_absolutelyContinuous_representative hab
  have hc := absolutelyContinuous_comp_contDiff hv hΦ
  apply (hasWeakDerivativeOnInterval_of_absolutelyContinuous hab hc).congr
    (huv.symm.mono fun _ ht => congrArg Φ ht)
  filter_upwards [ae_restrict_of_ae hv.ae_differentiableAt,
    ae_restrict_mem measurableSet_Icc, huv, hdv] with t ht hm hut hdt
  have hvd := ht (by simpa only [uIcc_of_le hab.le] using hm)
  have hder := ((hΦ.differentiable (by simp) (v t)).hasDerivAt.comp t hvd.hasDerivAt).deriv
  simpa only [Function.comp_def, ← hut, hdt] using hder

end PDE
