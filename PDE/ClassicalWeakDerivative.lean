import PDE.WeakDerivativeOn
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Classical derivatives are weak derivatives

The proof uses Mathlib's integration-by-parts theorem for Fréchet derivatives, not an
assumed weak identity. Compact support justifies every integral, even if `u` is only
`C¹` inside the open domain and has arbitrary behavior outside it.
-/

open MeasureTheory Set

namespace PDE

theorem hasWeakPartialOn_of_contDiffOn {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (i : Fin n) {u : Space n → ℝ} (hu : ContDiffOn ℝ 1 u Ω) :
    HasWeakPartialOn Ω i u (coordDeriv i u) := by
  have hlu : LocallyIntegrableOn u Ω volume :=
    hu.continuousOn.locallyIntegrableOn hΩ.measurableSet
  have hcd : ContinuousOn (coordDeriv i u) Ω :=
    (hu.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
  have hld : LocallyIntegrableOn (coordDeriv i u) Ω volume :=
    hcd.locallyIntegrableOn hΩ.measurableSet
  refine ⟨hlu, hld, ?_⟩
  intro φ hφ
  rw [setIntegral_mul_eq_integral_of_tsupport_subset _ _ (hφ.coordDeriv_tsupport_subset i),
    setIntegral_mul_eq_integral_of_tsupport_subset _ _ hφ.tsupport_subset]
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact integrable_mul_of_locallyIntegrableOn hld hφ.contDiff.continuous
      hφ.hasCompactSupport hφ.tsupport_subset
  · exact integrable_mul_of_locallyIntegrableOn hlu (hφ.coordDeriv_continuous i)
      (hφ.coordDeriv_hasCompactSupport i) (hφ.coordDeriv_tsupport_subset i)
  · exact integrable_mul_of_locallyIntegrableOn hlu hφ.contDiff.continuous
      hφ.hasCompactSupport hφ.tsupport_subset
  · intro x hx
    exact (hu.differentiableOn (by simp) x (hφ.tsupport_subset hx)).differentiableAt
      (hΩ.mem_nhds (hφ.tsupport_subset hx))
  · intro x _
    exact hφ.contDiff.differentiable (by simp) x

theorem hasWeakPartial_of_contDiff {n : ℕ} (i : Fin n) {u : Space n → ℝ}
    (hu : ContDiff ℝ 1 u) : HasWeakPartial i u (coordDeriv i u) :=
  hasWeakPartialOn_univ_iff.mp (hasWeakPartialOn_of_contDiffOn isOpen_univ i hu.contDiffOn)

end PDE
