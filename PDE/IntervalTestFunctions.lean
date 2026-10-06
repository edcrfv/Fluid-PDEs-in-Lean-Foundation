import PDE.WeakIntervalPoincare
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Compact smooth tests on an open interval

A zero-integral compact smooth test has a compact smooth primitive supported
in the same open interval. A normalized bump supplies the constant mode.
These are the test-function ingredients for reconstructing a representative
directly from distributional differentiation, without stronger boundary tests.
-/

open MeasureTheory Set
open scoped ContDiff

namespace PDE

/-- A normalized smooth bump supported strictly inside a nonempty interval. -/
theorem exists_normalized_interval_test {a b : ℝ} (hab : a < b) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ioo a b ∧ (∫ x, ψ x) = 1 := by
  let c : ℝ := (a + b) / 2
  let bump : ContDiffBump c :=
    ⟨(b - a) / 8, (b - a) / 4, by linarith, by linarith⟩
  refine ⟨bump.normed volume, bump.contDiff_normed, bump.hasCompactSupport_normed, ?_,
    bump.integral_normed⟩
  rw [bump.tsupport_normed_eq, Real.closedBall_eq_Icc]
  intro x hx
  dsimp [bump, c] at hx
  constructor <;> linarith [hx.1, hx.2]

private theorem compact_support_inside_interval {a b : ℝ} {φ : ℝ → ℝ}
    (hab : a < b) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioo a b) :
    ∃ c d : ℝ, a < c ∧ d < b ∧ tsupport φ ⊆ Ioo c d := by
  let K := tsupport φ ∪ {(a + b) / 2}
  have hK : IsCompact K := hc.isCompact.union isCompact_singleton
  have hKn : K.Nonempty := ⟨(a + b) / 2, Or.inr rfl⟩
  have hKs : K ⊆ Ioo a b := by
    intro x hx
    rcases hx with hx | hx
    · exact hs hx
    · have hx' : x = (a + b) / 2 := hx
      rw [hx']
      constructor <;> linarith
  obtain ⟨l, hl⟩ := hK.exists_isLeast hKn
  obtain ⟨r, hr⟩ := hK.exists_isGreatest hKn
  obtain ⟨c, hac, hcl⟩ := exists_between (hKs hl.1).1
  obtain ⟨d, hrd, hdb⟩ := exists_between (hKs hr.1).2
  refine ⟨c, d, hac, hdb, fun x hx => ?_⟩
  exact ⟨hcl.trans_le (hl.2 (Or.inl hx)), (hr.2 (Or.inl hx)).trans_lt hrd⟩

/-- A zero-integral compact smooth function on an interval is the derivative
of another compact smooth function supported strictly inside that interval. -/
theorem exists_compact_primitive_on_interval {a b : ℝ} {φ : ℝ → ℝ}
    (hab : a < b) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo a b) (hzero : (∫ x, φ x) = 0) :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Ioo a b ∧ ∀ x, HasDerivAt η (φ x) x := by
  obtain ⟨c, d, hac, hdb, hcd⟩ := compact_support_inside_interval hab hc hs
  let η := fun x => ∫ t in c..x, φ t
  have hdη : ∀ x, HasDerivAt η (φ x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hφ.continuous.intervalIntegrable c x)
      (hφ.continuous.stronglyMeasurableAtFilter volume (nhds x)) hφ.continuous.continuousAt
  have hηsmooth : ContDiff ℝ ∞ η := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun x => (hdη x).differentiableAt, ?_⟩
    have heq : deriv η = φ := funext fun x => (hdη x).deriv
    rwa [heq]
  have hleft (x : ℝ) (hx : x ≤ c) : η x = 0 := by
    change (∫ t in c..x, φ t) = 0
    calc
      _ = ∫ _t in c..x, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ≤ c := by simpa only [max_eq_left hx] using ht.2
        exact image_eq_zero_of_notMem_tsupport (fun hm => (hcd hm).1.not_ge ht')
      _ = 0 := by simp
  have hright (x : ℝ) (hx : d ≤ x) : η x = 0 := by
    change (∫ t in c..x, φ t) = 0
    rw [intervalIntegral.integral_eq_integral_of_support_subset, hzero]
    intro t ht
    have h := hcd (subset_tsupport φ ht)
    exact ⟨h.1, h.2.le.trans hx⟩
  have hηsupport : tsupport η ⊆ Icc c d := by
    apply closure_minimal ?_ isClosed_Icc
    intro x hx
    constructor
    · by_contra h
      exact hx (hleft x (le_of_not_ge h))
    · by_contra h
      exact hx (hright x (le_of_not_ge h))
  exact ⟨η, hηsmooth, isCompact_Icc.of_isClosed_subset (isClosed_tsupport η) hηsupport,
    fun x hx => ⟨hac.trans_le (hηsupport hx).1, (hηsupport hx).2.trans_lt hdb⟩, hdη⟩

end PDE
