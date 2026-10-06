import PDE.SobolevH1
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Identify weak derivatives after a bounded a.e. value limit and weak L²
derivative convergence. This can be applied coordinate by coordinate; no time
derivative or strong convergence of the spatial gradients is required. -/

open MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace PDE

/-- The integration-by-parts identity survives bounded a.e. convergence of
the values and weak L² convergence of one derivative. -/
theorem HasWeakPartialOn.of_bounded_ae_of_weak_L2
    {n : ℕ} {Ω : Set (Space n)} [IsFiniteMeasure (volume.restrict Ω)] {i : Fin n}
    {f : ℕ → Space n → ℝ} {g : Space n → ℝ}
    {d : ℕ → DomainL2 Ω} {v : DomainL2 Ω} {K : ℝ}
    (hf : ∀ j, AEStronglyMeasurable (f j) (volume.restrict Ω))
    (hg : AEStronglyMeasurable g (volume.restrict Ω))
    (hfK : ∀ j, ∀ᵐ x ∂volume.restrict Ω, ‖f j x‖ ≤ K)
    (hgK : ∀ᵐ x ∂volume.restrict Ω, ‖g x‖ ≤ K)
    (hfg : ∀ᵐ x ∂volume.restrict Ω, Tendsto (fun j => f j x) atTop (𝓝 (g x)))
    (hd : ∀ w : DomainL2 Ω,
      Tendsto (fun j => inner ℝ (d j) w) atTop (𝓝 (inner ℝ v w)))
    (hw : ∀ j, HasWeakPartialOn Ω i (f j) (d j)) :
    HasWeakPartialOn Ω i g v := by
  refine ⟨locallyIntegrableOn_of_locallyIntegrable_restrict
    ((MemLp.of_bound (p := 2) hg K hgK).locallyIntegrable (by norm_num)),
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp v).locallyIntegrable (by norm_num)), ?_⟩
  intro φ hφ
  have hφ2 : MemLp φ 2 (volume.restrict Ω) :=
    hφ.contDiff.continuous.memLp_of_hasCompactSupport hφ.hasCompactSupport
  have hleft : Tendsto (fun j => ∫ x in Ω, f j x * coordDeriv i φ x) atTop
      (𝓝 (∫ x in Ω, g x * coordDeriv i φ x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => K * ‖coordDeriv i φ x‖)
    · intro j
      exact (hf j).mul (hφ.coordDeriv_continuous i).aestronglyMeasurable
    · exact ((hφ.coordDeriv_continuous i).integrable_of_hasCompactSupport
        (hφ.coordDeriv_hasCompactSupport i)).norm.const_mul K
    · intro j
      filter_upwards [hfK j] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    · filter_upwards [hfg] with x hx
      exact hx.mul_const _
  have heq (z : DomainL2 Ω) : inner ℝ z (hφ2.toLp φ) = ∫ x in Ω, z x * φ x := by
    rw [real_inner_comm]
    exact testPairing_apply Ω φ hφ.contDiff.continuous hφ.hasCompactSupport z
  have hright : Tendsto (fun j => -(∫ x in Ω, d j x * φ x)) atTop
      (𝓝 (-(∫ x in Ω, v x * φ x))) := by
    simpa only [heq] using (hd (hφ2.toLp φ)).neg
  exact tendsto_nhds_unique hleft
    (hright.congr (fun j => (hw j).integration_by_parts φ hφ |>.symm))

end PDE
