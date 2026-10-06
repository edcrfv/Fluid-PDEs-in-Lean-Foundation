import PDE.IntervalWeakChainRule
import PDE.CubePoincare

/-! Bounds on interval weak derivatives, with unrestricted endpoint traces. -/

open MeasureTheory Set

namespace PDE

/-- Every pair of values of an AC representative is controlled by its L¹
derivative on the whole interval, in either ordering of the two points. -/
theorem abs_sub_le_integral_abs_deriv {a b x y : ℝ} {v : ℝ → ℝ}
    (hab : a ≤ b) (hv : AbsolutelyContinuousOnInterval v a b)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |v x - v y| ≤ ∫ t in Icc a b, |deriv v t| := by
  have hsub : uIcc y x ⊆ Icc a b := uIcc_subset_Icc hy hx
  have hxy : AbsolutelyContinuousOnInterval v y x :=
    hv.mono (by simpa only [uIcc_of_le hab] using hsub)
  have hi : IntegrableOn (fun t => |deriv v t|) (Icc a b) :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hv.intervalIntegrable_deriv).abs
  calc
    _ = |∫ t in y..x, deriv v t| := congrArg abs hxy.integral_deriv_eq_sub.symm
    _ ≤ ∫ t in uIoc y x, |deriv v t| := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm_uIoc (f := deriv v) (a := y) (b := x))
    _ ≤ _ := setIntegral_mono_set hi (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (Filter.Eventually.of_forall fun _ ht => hsub (uIoc_subset_uIcc ht))

/-- Actual compact-test W¹,¹ differentiation on the unit interval gives the
essential supremum estimate. No representative or boundary value is assumed. -/
theorem HasWeakDerivativeOnInterval.ae_abs_le_integral_abs
    {u du : ℝ → ℝ} (hu : HasWeakDerivativeOnInterval 0 1 u du) :
    ∀ᵐ t ∂unitIntervalMeasure,
      |u t| ≤ (∫ s, |u s| ∂unitIntervalMeasure) + ∫ s, |du s| ∂unitIntervalMeasure := by
  obtain ⟨v, hv, huv, hdv⟩ := hu.exists_absolutelyContinuous_representative (by norm_num)
  have hvi : Integrable v unitIntervalMeasure := hu.integrable.congr huv
  have hid : (∫ s, |deriv v s| ∂unitIntervalMeasure) =
      ∫ s, |du s| ∂unitIntervalMeasure := integral_congr_ae (hdv.mono fun _ h => congrArg abs h)
  have hiu : (∫ s, |v s| ∂unitIntervalMeasure) =
      ∫ s, |u s| ∂unitIntervalMeasure := integral_congr_ae (huv.symm.mono fun _ h => congrArg abs h)
  filter_upwards [huv, ae_restrict_mem measurableSet_Icc] with t hut ht
  rw [hut, ← hid, ← hiu]
  have hp : ∀ᵐ s ∂unitIntervalMeasure,
      |v t| ≤ |v s| + ∫ r, |deriv v r| ∂unitIntervalMeasure := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hb := abs_sub_le_integral_abs_deriv (by norm_num) hv ht hs
    change |v t - v s| ≤ ∫ r, |deriv v r| ∂unitIntervalMeasure at hb
    have ht' : |v t| ≤ |v t - v s| + |v s| := by
      simpa only [sub_add_cancel] using abs_add_le (v t - v s) (v s)
    linarith
  have h := integral_mono_ae (integrable_const |v t|)
    (hvi.abs.add (integrable_const _)) hp
  change (∫ _, |v t| ∂unitIntervalMeasure) ≤
    ∫ s, |v s| + (∫ r, |deriv v r| ∂unitIntervalMeasure) ∂unitIntervalMeasure at h
  simpa only [integral_add hvi.abs (integrable_const _), integral_const,
    probReal_univ, smul_eq_mul, one_mul] using h

/-- The same bound in extended norms, for direct use in product integrals. -/
theorem HasWeakDerivativeOnInterval.ae_enorm_le_lintegral_enorm
    {u du : ℝ → ℝ} (hu : HasWeakDerivativeOnInterval 0 1 u du) :
    ∀ᵐ t ∂unitIntervalMeasure,
      ‖u t‖ₑ ≤ (∫⁻ s, ‖u s‖ₑ ∂unitIntervalMeasure) + ∫⁻ s, ‖du s‖ₑ ∂unitIntervalMeasure := by
  filter_upwards [hu.ae_abs_le_integral_abs] with t ht
  have h := ENNReal.ofReal_le_ofReal ht
  rw [ENNReal.ofReal_add (integral_nonneg fun _ => abs_nonneg _)
    (integral_nonneg fun _ => abs_nonneg _)] at h
  have hui : Integrable u unitIntervalMeasure := hu.integrable
  have hdi : Integrable du unitIntervalMeasure := hu.derivative_integrable
  simpa only [← Real.norm_eq_abs, ofReal_norm,
    ofReal_integral_norm_eq_lintegral_enorm hui,
    ofReal_integral_norm_eq_lintegral_enorm hdi] using h

end PDE
