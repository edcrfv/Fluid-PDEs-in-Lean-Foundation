import PDE.SobolevZero
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Density of the zero-boundary energy space in L²

The value map is injective and norm decreasing, and its range is dense on every open
domain. Orthogonality to all compact smooth tests forces an L² function to vanish a.e.;
the Hilbert-space orthogonal-complement theorem then gives density.
-/

open MeasureTheory InnerProductSpace Set
open scoped ENNReal
namespace PDE
namespace H10
variable {n : ℕ} {Ω : Set (Space n)} {hΩ : IsOpen Ω}

noncomputable def value (Ω : Set (Space n)) (hΩ : IsOpen Ω) : H10 Ω hΩ →L[ℝ] DomainL2 Ω :=
  (H1.value Ω).comp (H10.toH1 Ω hΩ)

theorem norm_value_le (u : H10 Ω hΩ) : ‖value Ω hΩ u‖ ≤ ‖u‖ := H1.norm_value_le u.val

theorem value_injective (Ω : Set (Space n)) (hΩ : IsOpen Ω) : Function.Injective (value Ω hΩ) := by
  intro u v huv
  exact Subtype.ext (H1.value_injective hΩ huv)

/-- The zero-boundary energy space is dense in L² on every open domain. -/
theorem value_denseRange (Ω : Set (Space n)) (hΩ : IsOpen Ω) : DenseRange (value Ω hΩ) := by
  let K : Submodule ℝ (DomainL2 Ω) := (value Ω hΩ).range
  have horth : Kᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff Kᗮ).mpr
    intro g hg
    apply Lp.ext
    have hloc : LocallyIntegrableOn (fun x => g x) Ω volume :=
      locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp g).locallyIntegrable (by norm_num))
    have hz : ∀ᵐ x ∂volume, x ∈ Ω → g x = 0 := by
      apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
      intro φ hφ hc hs
      let ht : IsTestFunctionOn Ω φ := ⟨hφ, hc, hs⟩
      have hi : inner ℝ g (value Ω hΩ (ofTestFunction hΩ φ ht)) = 0 :=
        K.inner_left_of_mem_orthogonal ⟨ofTestFunction hΩ φ ht, rfl⟩ hg
      have hae : value Ω hΩ (ofTestFunction hΩ φ ht) =ᵐ[volume.restrict Ω] φ :=
        H1.value_ofTestFunction_ae φ ht
      have hpair : (∫ x in Ω, g x * φ x) = 0 := by
        rw [← hi, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hae] with x hx
        simp [hx, mul_comm]
      have hglobal : (∫ x, g x * φ x) = 0 := by
        rw [← setIntegral_mul_eq_integral_of_tsupport_subset _ _ hs]
        exact hpair
      simpa only [smul_eq_mul, mul_comm] using hglobal
    have hzero : g =ᵐ[volume.restrict Ω] (fun _ => 0) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' hΩ.measurableSet]
      exact hz
    exact hzero.trans (Lp.coeFn_zero ℝ 2 (volume.restrict Ω)).symm
  have htop : K.topologicalClosure = ⊤ := by
    rw [← K.orthogonal_orthogonal_eq_closure, horth, Submodule.bot_orthogonal_eq_top]
  exact K.dense_iff_topologicalClosure_eq_top.mpr htop
end H10
end PDE
