import PDE.TimePairing
import PDE.WeakTimeDerivative

/-!
# Linear tests for weak Bochner convergence

L² time weights and arbitrary continuous spatial functionals define continuous
linear tests on Bochner L². Riesz representation passes them through weak convergence.
-/

open InnerProductSpace MeasureTheory Set Filter
open scoped Topology
namespace PDE
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- An L² time weight paired with any continuous scalar spatial functional. -/
noncomputable def weightedTimeFunctional (g : Lp ℝ 2 μ) (ℓ : V →L[ℝ] ℝ) : Lp V 2 μ →L[ℝ] ℝ :=
  (innerSL ℝ g).comp (ℓ.compLpL 2 μ)

theorem weightedTimeFunctional_apply (g : Lp ℝ 2 μ) (ℓ : V →L[ℝ] ℝ) (u : Lp V 2 μ) :
    weightedTimeFunctional g ℓ u = ∫ t, g t * ℓ (u t) ∂μ := by
  change inner ℝ g (ℓ.compLpL 2 μ u) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ℓ.coeFn_compLpL u] with t ht
  simp [ht, mul_comm]

theorem weightedTimeFunctional_tendsto [CompleteSpace V] (g : Lp ℝ 2 μ) (ℓ : V →L[ℝ] ℝ)
    (u : ℕ → Lp V 2 μ) (w : Lp V 2 μ)
    (hu : ∀ z : Lp V 2 μ, Tendsto (fun k => inner ℝ (u k) z) atTop (𝓝 (inner ℝ w z))) :
    Tendsto (fun k => weightedTimeFunctional g ℓ (u k)) atTop (𝓝 (weightedTimeFunctional g ℓ w)) := by
  have ht := hu ((toDual ℝ (Lp V 2 μ)).symm (weightedTimeFunctional g ℓ))
  have he (x : Lp V 2 μ) :
      inner ℝ x ((toDual ℝ (Lp V 2 μ)).symm (weightedTimeFunctional g ℓ)) =
        weightedTimeFunctional g ℓ x := by rw [real_inner_comm, toDual_symm_apply]
  simpa only [he] using ht

/-- Continuous scalar weights and arbitrary spatial functionals pass through weak time-L² limits. -/
theorem timeL2_weighted_clm_tendsto [CompleteSpace V] {a b : ℝ} (g : ℝ → ℝ) (hg : Continuous g)
    (ℓ : V →L[ℝ] ℝ) (u : ℕ → TimeL2 V a b) (w : TimeL2 V a b)
    (hu : ∀ z : TimeL2 V a b, Tendsto (fun k => inner ℝ (u k) z) atTop (𝓝 (inner ℝ w z))) :
    Tendsto (fun k => ∫ t in Icc a b, g t * ℓ (u k t)) atTop
      (𝓝 (∫ t in Icc a b, g t * ℓ (w t))) := by
  have hg2 : MemLp g 2 (volume.restrict (Icc a b)) :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr ((hg.pow 2).integrableOn_Icc)
  let gl := hg2.toLp g
  have he (v : TimeL2 V a b) : weightedTimeFunctional gl ℓ v =
      ∫ t in Icc a b, g t * ℓ (v t) := by
    rw [weightedTimeFunctional_apply]
    apply integral_congr_ae
    filter_upwards [hg2.coeFn_toLp] with t ht
    rw [ht]
  simpa only [he] using weightedTimeFunctional_tendsto gl ℓ u w hu
end PDE
