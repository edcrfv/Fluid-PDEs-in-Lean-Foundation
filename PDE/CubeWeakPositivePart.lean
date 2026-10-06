import PDE.CubeWeakReassembly
import PDE.IntervalWeakPositivePart

/-! Actual weak gradients of positive parts on cubes. There is no zero-trace
assumption, and all input representatives need only be a.e. measurable. -/

open MeasureTheory Set
open scoped ENNReal

namespace PDE

theorem memLp_positivePart_derivative {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {u du : α → ℝ} {p : ℝ≥0∞}
    (hu : AEMeasurable u μ) (hd : MemLp du p μ) :
    MemLp (fun x => if 0 < u x then du x else 0) p μ := by
  have h := hd.indicator (measurableSet_lt (measurable_const (a := (0 : ℝ))) hu.measurable_mk)
  apply h.ae_eq
  filter_upwards [hu.ae_eq_mk] with x hx
  simp only [Set.indicator, mem_ofPred_eq, hx]

/-- The positive part has the expected actual spatial weak partial, including
on the zero level, without assuming that this level has measure zero. -/
theorem HasWeakPartialOn.unitOpenCube_positivePart {n : ℕ}
    {i : Fin (n + 1)} {u du : Space (n + 1) → ℝ}
    (hw : HasWeakPartialOn (unitOpenCube (n + 1)) i u du)
    (hu : MemLp u 2 (volume.restrict (unitOpenCube (n + 1))))
    (hd : MemLp du 2 (volume.restrict (unitOpenCube (n + 1)))) :
    HasWeakPartialOn (unitOpenCube (n + 1)) i (fun x => max (u x) 0)
      (fun x => if 0 < u x then du x else 0) := by
  apply hasWeakPartialOn_unitOpenCube_of_weak_slices hu.pos_part
    (memLp_positivePart_derivative hu.aestronglyMeasurable.aemeasurable hd)
  filter_upwards [hw.ae_unitOpenCube_update_slices hu hd] with x hx
  exact hx.positivePart (by norm_num)

/-- The spatial weak derivative vanishes a.e. on every prescribed level,
including level sets of positive measure. -/
theorem HasWeakPartialOn.unitOpenCube_ae_zero_on_level {n : ℕ}
    {i : Fin (n + 1)} {u du : Space (n + 1) → ℝ}
    (hw : HasWeakPartialOn (unitOpenCube (n + 1)) i u du)
    (hu : MemLp u 2 (volume.restrict (unitOpenCube (n + 1))))
    (hd : MemLp du 2 (volume.restrict (unitOpenCube (n + 1)))) (c : ℝ) :
    ∀ᵐ x ∂volume.restrict (unitOpenCube (n + 1)), u x = c → du x = 0 := by
  let hm := hu.aestronglyMeasurable.aemeasurable
  let hdm := hd.aestronglyMeasurable.aemeasurable
  have hw' := hw.congr hm.ae_eq_mk hdm.ae_eq_mk
  have hs := hw'.ae_unitOpenCube_update_slices
    (hu.ae_eq hm.ae_eq_mk) (hd.ae_eq hdm.ae_eq_mk)
  have hp : MeasurableSet {x | hm.mk u x = c → hdm.mk du x = 0} := by
    have h1 := measurableSet_eq_fun hm.measurable_mk (measurable_const (a := c))
    have h2 := measurableSet_eq_fun hdm.measurable_mk (measurable_const (a := (0 : ℝ)))
    have he : {x | hm.mk u x = c → hdm.mk du x = 0} =
        {x | hm.mk u x = c}ᶜ ∪ {x | hdm.mk du x = 0} := by
      ext x
      simp only [mem_union, mem_compl_iff, mem_ofPred_eq, imp_iff_not_or]
    rw [he]
    exact h1.compl.union h2
  have ha := ae_unitOpenCube_of_ae_update i hp
    (hs.mono fun _ hx => hx.ae_zero_on_level (by norm_num) c)
  filter_upwards [ha, hm.ae_eq_mk, hdm.ae_eq_mk] with x hx he hde
  simpa only [← he, ← hde] using hx

/-- Changing a scalar slope at one temperature level does not change its
product with the spatial weak derivative. This does not apply to source terms
which are not multiplied by that derivative. -/
theorem HasWeakPartialOn.unitOpenCube_slope_congr {n : ℕ}
    {i : Fin (n + 1)} {u du : Space (n + 1) → ℝ}
    (hw : HasWeakPartialOn (unitOpenCube (n + 1)) i u du)
    (hu : MemLp u 2 (volume.restrict (unitOpenCube (n + 1))))
    (hd : MemLp du 2 (volume.restrict (unitOpenCube (n + 1))))
    {F G : ℝ → ℝ} {c : ℝ} (hFG : ∀ s, s ≠ c → F s = G s) :
    (fun x => F (u x) * du x) =ᵐ[volume.restrict (unitOpenCube (n + 1))]
      (fun x => G (u x) * du x) := by
  filter_upwards [hw.unitOpenCube_ae_zero_on_level hu hd c] with x hx
  by_cases hc : u x = c
  · simp only [hx hc, mul_zero]
  · rw [hFG _ hc]

end PDE
