import PDE.UnitCubeCoordinates

/-! Weak coordinate-line derivatives on actual open cubes, and the a.e.
Fubini transfer needed to evaluate a line estimate at the base point. -/

open MeasureTheory Set

namespace PDE

private theorem first_update_slices {n : ℕ} {u du : Space (n + 1) → ℝ}
    (hw : HasWeakPartialOn (unitOpenCube (n + 1)) 0 u du)
    (hu : MemLp u 2 (volume.restrict (unitOpenCube (n + 1))))
    (hd : MemLp du 2 (volume.restrict (unitOpenCube (n + 1)))) :
    ∀ᵐ x ∂volume.restrict (unitOpenCube (n + 1)),
      HasWeakDerivativeOnInterval 0 1 (fun t => u (Function.update x 0 t))
        (fun t => du (Function.update x 0 t)) := by
  rw [unitOpenCube_succ] at hw hu hd
  have hs := hw.ae_interval_slices (isOpen_unitOpenCube n) hu hd
  have hp := (Measure.quasiMeasurePreserving_snd (μ := unitIntervalMeasure)).tendsto_ae.eventually hs
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => unitIntervalMeasure) 0
  rw [← unitOpenCube_measure_eq, ← unitOpenCube_measure_eq] at he
  have hf := he.quasiMeasurePreserving.tendsto_ae.eventually hp
  filter_upwards [hf] with x hx
  have hupdate (t : ℝ) : Function.update x 0 t = Fin.cons t (Fin.tail x) := by
    rw [← Fin.cons_self_tail x, Fin.update_cons_zero, Fin.tail_cons]
  change HasWeakDerivativeOnInterval 0 1 (fun t => u (Fin.cons t (Fin.tail x)))
    (fun t => du (Fin.cons t (Fin.tail x))) at hx
  simpa only [hupdate] using hx

/-- Every actual H¹ weak partial supplies compact-test weak differentiation
along almost every line in its own coordinate direction. -/
theorem HasWeakPartialOn.ae_unitOpenCube_update_slices {n : ℕ}
    {i : Fin (n + 1)} {u du : Space (n + 1) → ℝ}
    (hw : HasWeakPartialOn (unitOpenCube (n + 1)) i u du)
    (hu : MemLp u 2 (volume.restrict (unitOpenCube (n + 1))))
    (hd : MemLp du 2 (volume.restrict (unitOpenCube (n + 1)))) :
    ∀ᵐ x ∂volume.restrict (unitOpenCube (n + 1)),
      HasWeakDerivativeOnInterval 0 1 (fun t => u (Function.update x i t))
        (fun t => du (Function.update x i t)) := by
  let e : Equiv.Perm (Fin (n + 1)) := Equiv.swap i 0
  have hw' := hw.permuteCoordinates (isOpen_unitOpenCube _).measurableSet hu hd e
  have hm := permuteCoordinates_measurePreserving e (isOpen_unitOpenCube (n + 1)).measurableSet
  rw [unitOpenCube_permute] at hw' hm
  have hei : e i = 0 := by simp [e]
  rw [hei] at hw'
  have hs := first_update_slices hw' (hu.comp_measurePreserving hm) (hd.comp_measurePreserving hm)
  have hs' := hm.quasiMeasurePreserving.tendsto_ae.eventually hs
  filter_upwards [hs'] with x hx
  have hinv : PDE.permuteCoordinates e (PDE.permuteCoordinates e x) = x := by
    simpa only [e, Equiv.symm_swap] using permuteCoordinates_inverse e x
  simpa only [permuteCoordinates_update, hinv, e, Equiv.symm_swap, Equiv.swap_apply_right] using hx

/-- If an assertion holds for almost every replacement of a coordinate,
for almost every base point, it holds almost everywhere in the cube itself. -/
theorem ae_unitOpenCube_of_ae_update {n : ℕ} (i : Fin (n + 1))
    {p : Space (n + 1) → Prop} (hp : MeasurableSet {x | p x})
    (h : ∀ᵐ x ∂volume.restrict (unitOpenCube (n + 1)),
      ∀ᵐ t ∂unitIntervalMeasure, p (Function.update x i t)) :
    ∀ᵐ x ∂volume.restrict (unitOpenCube (n + 1)), p x := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => unitIntervalMeasure) i
  rw [← unitOpenCube_measure_eq, ← unitOpenCube_measure_eq] at he
  have h' := (he.symm e).quasiMeasurePreserving.tendsto_ae.eventually h
  simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.update_insertNth] at h'
  obtain ⟨_a, ha⟩ := (Measure.ae_ae_of_ae_prod h').exists
  have hp' : MeasurableSet {z : ℝ × Space n | p (i.insertNth z.1 z.2)} :=
    hp.preimage e.symm.measurable
  have ht : ∀ᵐ z ∂unitIntervalMeasure.prod (volume.restrict (unitOpenCube n)),
      p (i.insertNth z.1 z.2) :=
    (Measure.ae_prod_iff_ae_ae hp').mpr ((Measure.ae_ae_comm hp').mpr ha)
  have hout := he.quasiMeasurePreserving.tendsto_ae.eventually ht
  change ∀ᵐ x ∂volume.restrict (unitOpenCube (n + 1)), p (e.symm (e x)) at hout
  simpa only [e.symm_apply_apply] using hout

end PDE
