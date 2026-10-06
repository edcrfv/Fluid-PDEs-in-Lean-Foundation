import Mathlib.MeasureTheory.Function.L2Space
import PDE.WeakCompactness

/-!
# Weighted linear tests on Bochner L²

An L² scalar time weight and a bounded bilinear spatial form define a bounded bilinear
pairing with an L² trajectory. The integral formula is justified by L² inner products,
and weak convergence passes through these tests by the Riesz representation theorem.
-/

open InnerProductSpace MeasureTheory Filter
open scoped Topology
namespace PDE
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {α : Type*} [MeasurableSpace α] {μ : Measure α}

noncomputable def weightedTimeForm (g : Lp ℝ 2 μ) (B : V →L[ℝ] V →L[ℝ] ℝ) :
    V →L[ℝ] Lp V 2 μ →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (Lp V 2 μ) (Lp ℝ 2 μ) ℝ) (innerSL ℝ g)).comp
    (B.compLpL₂ 2 μ)

theorem weightedTimeForm_apply (g : Lp ℝ 2 μ) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (v : V) (u : Lp V 2 μ) : weightedTimeForm g B v u = ∫ t, g t * B v (u t) ∂μ := by
  change inner ℝ g ((B v).compLpL 2 μ u) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(B v).coeFn_compLpL u] with t ht
  simp [ht, mul_comm]

theorem weightedTimeForm_integrable (g : Lp ℝ 2 μ) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (v : V) (u : Lp V 2 μ) : Integrable (fun t => g t * B v (u t)) μ := by
  have hi := L2.integrable_inner (𝕜 := ℝ) g ((B v).compLpL 2 μ u)
  apply hi.congr
  filter_upwards [(B v).coeFn_compLpL u] with t ht
  simp [ht, mul_comm]

theorem weightedTimeForm_tendsto [CompleteSpace V] (g : Lp ℝ 2 μ)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (v : V) (u : ℕ → Lp V 2 μ) (w : Lp V 2 μ)
    (hu : ∀ z : Lp V 2 μ, Tendsto (fun k => inner ℝ (u k) z) atTop (𝓝 (inner ℝ w z))) :
    Tendsto (fun k => weightedTimeForm g B v (u k)) atTop (𝓝 (weightedTimeForm g B v w)) := by
  have h := hu ((toDual ℝ (Lp V 2 μ)).symm (weightedTimeForm g B v))
  have he (x : Lp V 2 μ) :
      inner ℝ x ((toDual ℝ (Lp V 2 μ)).symm (weightedTimeForm g B v)) =
        weightedTimeForm g B v x := by rw [real_inner_comm, toDual_symm_apply]
  simpa only [he] using h
end PDE
