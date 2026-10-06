import PDE.CubeWeakSlices
import Mathlib.Analysis.Calculus.Deriv.Pi

/-! Reassembling weak line derivatives into the actual multidimensional
distributional identity. This is the converse needed for Sobolev chain rules;
linewise identities are not silently identified with spatial weak derivatives. -/

open MeasureTheory Set
open scoped ContDiff

namespace PDE

/-- Spatial a.e. statements remain valid on almost every coordinate line.
No pointwise representative or measurability of the predicate is required. -/
theorem ae_unitOpenCube_update_of_ae {n : ℕ} (i : Fin (n + 1))
    {p : Space (n + 1) → Prop}
    (h : ∀ᵐ x ∂volume.restrict (unitOpenCube (n + 1)), p x) :
    ∀ᵐ x ∂volume.restrict (unitOpenCube (n + 1)),
      ∀ᵐ t ∂unitIntervalMeasure, p (Function.update x i t) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => unitIntervalMeasure) i
  rw [← unitOpenCube_measure_eq, ← unitOpenCube_measure_eq] at he
  have hs := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := volume.restrict (unitOpenCube n))
      (ν := unitIntervalMeasure)).quasiMeasurePreserving.tendsto_ae.eventually
      ((he.symm e).quasiMeasurePreserving.tendsto_ae.eventually h))
  have hp := (Measure.quasiMeasurePreserving_snd (μ := unitIntervalMeasure)).tendsto_ae.eventually hs
  have hf := he.quasiMeasurePreserving.tendsto_ae.eventually hp
  filter_upwards [hf] with x hx
  change ∀ᵐ t ∂unitIntervalMeasure, p (i.insertNth t (i.removeNth x)) at hx
  simpa only [Fin.insertNth_removeNth] using hx

theorem deriv_testFunction_update {n : ℕ} {Ω : Set (Space n)}
    {φ : Space n → ℝ} (hφ : IsTestFunctionOn Ω φ) (x : Space n) (i : Fin n) (t : ℝ) :
    deriv (fun s => φ (Function.update x i s)) t = coordDeriv i φ (Function.update x i t) := by
  exact ((hφ.contDiff.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_update x i t)).deriv

/-- A compact spatial test restricts to a legal compact interval test on every
coordinate line, even when its base point is outside the support. -/
theorem IsTestFunctionOn.unitOpenCube_update {n : ℕ} {φ : Space n → ℝ}
    (hφ : IsTestFunctionOn (unitOpenCube n) φ) (x : Space n) (i : Fin n) :
    ContDiff ℝ ∞ (fun t => φ (Function.update x i t)) ∧
      HasCompactSupport (fun t => φ (Function.update x i t)) ∧
        tsupport (fun t => φ (Function.update x i t)) ⊆ Ioo 0 1 := by
  have hs : tsupport (fun t => φ (Function.update x i t)) ⊆ Ioo 0 1 := by
    intro t ht
    have hm := tsupport_comp_subset_preimage φ
      (contDiff_update (𝕜 := ℝ) (∞ : ℕ∞ω) x i).continuous ht
    simpa using hφ.tsupport_subset hm i
  exact ⟨hφ.contDiff.comp (contDiff_update _ x i),
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hs.trans Ioo_subset_Icc_self), hs⟩

/-- The converse to weak slicing on cubes. The conclusion tests against every
compact smooth multidimensional function and records actual local integrability. -/
theorem hasWeakPartialOn_unitOpenCube_of_weak_slices {n : ℕ}
    {i : Fin (n + 1)} {u du : Space (n + 1) → ℝ}
    (hu : MemLp u 2 (volume.restrict (unitOpenCube (n + 1))))
    (hd : MemLp du 2 (volume.restrict (unitOpenCube (n + 1))))
    (hw : ∀ᵐ x ∂volume.restrict (unitOpenCube (n + 1)),
      HasWeakDerivativeOnInterval 0 1 (fun t => u (Function.update x i t))
        (fun t => du (Function.update x i t))) :
    HasWeakPartialOn (unitOpenCube (n + 1)) i u du := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => unitIntervalMeasure) i
  rw [← unitOpenCube_measure_eq, ← unitOpenCube_measure_eq] at he
  have hi := he.symm e
  have hw' := hi.quasiMeasurePreserving.tendsto_ae.eventually hw
  simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.update_insertNth] at hw'
  obtain ⟨_a, hs⟩ := (Measure.ae_ae_of_ae_prod hw').exists
  have huloc := locallyIntegrableOn_of_locallyIntegrable_restrict
    (hu.locallyIntegrable (by norm_num))
  have hdloc := locallyIntegrableOn_of_locallyIntegrable_restrict
    (hd.locallyIntegrable (by norm_num))
  refine ⟨huloc, hdloc, ?_⟩
  intro φ hφ
  have hleft := (integrable_mul_of_locallyIntegrableOn huloc
    (hφ.coordDeriv_continuous i) (hφ.coordDeriv_hasCompactSupport i)
    (hφ.coordDeriv_tsupport_subset i)).restrict (s := unitOpenCube (n + 1))
  have hright := (integrable_mul_of_locallyIntegrableOn hdloc
    hφ.contDiff.continuous hφ.hasCompactSupport hφ.tsupport_subset).restrict
      (s := unitOpenCube (n + 1))
  have hl := hi.integral_comp' (fun x => u x * coordDeriv i φ x)
  have hr := hi.integral_comp' (fun x => du x * φ x)
  have hli := hi.integrable_comp_of_integrable hleft
  have hri := hi.integrable_comp_of_integrable hright
  simp only [Function.comp_def] at hli hri
  rw [← hl, ← hr, integral_prod_symm _ hli, integral_prod_symm _ hri, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hs] with y hy
  have ht := hφ.unitOpenCube_update (i.insertNth 0 y) i
  have htest := hy.integration_by_parts (fun t => φ (i.insertNth t y))
    (by simpa only [Fin.update_insertNth] using ht.1)
    (by simpa only [Fin.update_insertNth] using ht.2.1)
    (by simpa only [Fin.update_insertNth] using ht.2.2)
  have hder (t : ℝ) : deriv (fun s => φ (i.insertNth s y)) t = coordDeriv i φ (i.insertNth t y) := by
    simpa only [Fin.update_insertNth] using deriv_testFunction_update hφ (i.insertNth 0 y) i t
  simpa only [unitIntervalMeasure, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_mk, hder, smul_eq_mul, mul_comm] using htest

end PDE
