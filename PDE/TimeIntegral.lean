import PDE.WeakTimeDerivative
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integration on the time triangle

For Bochner integrable functions, Fubini exchanges a weighted past integral with a
future scalar integral. The proof verifies integrability of the triangular kernel,
then identifies each section of its indicator. This is used to reconstruct time traces.
-/

open MeasureTheory Set
namespace PDE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Fubini on the time triangle: the past-integral operator is paired with a future integral. -/
theorem integral_past_smul_eq_future_smul {a b : ℝ} {g : ℝ → ℝ} {u : ℝ → E}
    (hg : IntegrableOn g (Icc a b)) (hu : IntegrableOn u (Icc a b)) :
    (∫ t in Icc a b, g t • (∫ s in Icc a t, u s)) =
      ∫ s in Icc a b, (∫ t in Icc s b, g t) • u s := by
  classical
  let K : ℝ → ℝ → E := fun t s => if s ≤ t then g t • u s else 0
  have hK : Integrable (Function.uncurry K)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))) := by
    change Integrable ({z : ℝ × ℝ | z.2 ≤ z.1}.indicator (fun z => g z.1 • u z.2)) _
    exact (hg.smul_prod hu).indicator (measurableSet_le measurable_snd measurable_fst)
  have hleft (t : ℝ) (ht : t ∈ Icc a b) :
      (∫ s in Icc a b, K t s) = g t • (∫ s in Icc a t, u s) := by
    have hs : Icc a b ∩ Iic t = Icc a t := by
      ext s
      simp only [mem_inter_iff, mem_Icc, mem_Iic]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans ht.2⟩, h.2⟩⟩
    change (∫ s in Icc a b, (Iic t).indicator (fun s => g t • u s) s) = _
    rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      inter_comm (Iic t), hs, integral_smul]
  have hright (s : ℝ) (hs : s ∈ Icc a b) :
      (∫ t in Icc a b, K t s) = (∫ t in Icc s b, g t) • u s := by
    have ht : Icc a b ∩ Ici s = Icc s b := by
      ext t
      simp only [mem_inter_iff, mem_Icc, mem_Ici]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hs.1.trans h.1, h.2⟩, h.1⟩⟩
    change (∫ t in Icc a b, (Ici s).indicator (fun t => g t • u s) t) = _
    rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
      inter_comm (Ici s), ht, integral_smul_const]
  calc
    (∫ t in Icc a b, g t • (∫ s in Icc a t, u s)) =
        ∫ t in Icc a b, ∫ s in Icc a b, K t s := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      exact (hleft t ht).symm
    _ = ∫ s in Icc a b, ∫ t in Icc a b, K t s := integral_integral_swap hK
    _ = ∫ s in Icc a b, (∫ t in Icc s b, g t) • u s := by
      apply setIntegral_congr_fun measurableSet_Icc
      exact hright
end PDE
