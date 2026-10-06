import PDE.OneSidedPositivePart

/-! Globally smooth, convex, nonincreasing approximations of `(C-z)₊`.
They vanish exactly above the comparison level and need no logarithmic domain. -/

namespace PDE

noncomputable def smoothDeficit (C σ z : ℝ) : ℝ := oneSidedPositivePart σ (C - z)

theorem hasDerivAt_smoothDeficit (C σ z : ℝ) :
    HasDerivAt (smoothDeficit C σ) (-oneSidedSlope σ (C - z)) z := by
  simpa only [mul_neg, mul_one] using! (hasDerivAt_oneSidedPositivePart σ (C - z)).comp z
    ((hasDerivAt_id z).const_sub C)

theorem hasDerivAt_deriv_smoothDeficit (C σ z : ℝ) :
    HasDerivAt (deriv (smoothDeficit C σ)) (oneSidedCurvature σ (C - z)) z := by
  have he : deriv (smoothDeficit C σ) = fun y => -oneSidedSlope σ (C - y) :=
    funext fun y => (hasDerivAt_smoothDeficit C σ y).deriv
  rw [he]
  simpa only [mul_neg, mul_one, neg_neg] using! ((hasDerivAt_oneSidedSlope σ (C - z)).comp z
    ((hasDerivAt_id z).const_sub C)).neg

theorem smoothDeficit_signs {σ : ℝ} (hσ : 0 < σ) (C z : ℝ) :
    0 ≤ smoothDeficit C σ z ∧ deriv (smoothDeficit C σ) z ≤ 0 ∧
      0 ≤ deriv (deriv (smoothDeficit C σ)) z := by
  rw [(hasDerivAt_smoothDeficit C σ z).deriv,
    (hasDerivAt_deriv_smoothDeficit C σ z).deriv]
  exact ⟨oneSidedPositivePart_nonneg hσ _, neg_nonpos.mpr (oneSidedSlope_bounds _ _).1,
    oneSidedCurvature_nonneg hσ _⟩

theorem smoothDeficit_zero {C σ z : ℝ} (hσ : 0 < σ) (hz : C ≤ z) :
    smoothDeficit C σ z = 0 := oneSidedPositivePart_zero hσ (sub_nonpos.mpr hz)

theorem le_add_of_smoothDeficit_zero {C σ z : ℝ} (hσ : 0 < σ)
    (hz : smoothDeficit C σ z = 0) : C ≤ z + σ := by
  have hh := (oneSidedPositivePart_error hσ (C - z)).2
  change max (C - z) 0 - smoothDeficit C σ z ≤ σ at hh
  rw [hz] at hh
  linarith [le_max_left (C - z) 0]

end PDE
