import PDE.SpatialWeakSlicing
import PDE.SobolevSlicing

/-! Spatial weak derivatives in vector space-time coordinates give genuine
spatial weak derivatives on a common a.e.-time set in product coordinates. -/

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace PDE

/-- Finite transverse volume gives finite space-time cylinder volume. -/
theorem isFiniteMeasure_intervalCylinder {n : ℕ} (a b : ℝ)
    {Ω : Set (Space n)} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)] :
    IsFiniteMeasure (volume.restrict (intervalCylinder a b Ω)) := by
  rw [← (cylinderLift_measurePreserving a b hΩ).map_eq]
  infer_instance

theorem coordDeriv_cylinder_product_succ {n : ℕ}
    {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) {ψ : Space n → ℝ}
    (hψ : Differentiable ℝ ψ) (i : Fin n) (x : Space (n + 1)) :
    coordDeriv i.succ (fun y => φ (y 0) * ψ (Fin.tail y)) x =
      φ (x 0) * coordDeriv i ψ (Fin.tail x) := by
  let p : Space (n + 1) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let q : Space (n + 1) →L[ℝ] Space n :=
    ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj j.succ)
  have hp : HasFDerivAt (fun y => φ (y 0)) (deriv φ (x 0) • p) x :=
    (hφ (x 0)).hasDerivAt.comp_hasFDerivAt x p.hasFDerivAt
  have hq : HasFDerivAt (fun y => ψ (Fin.tail y)) ((fderiv ℝ ψ (Fin.tail x)).comp q) x :=
    (hψ (Fin.tail x)).hasFDerivAt.comp x q.hasFDerivAt
  have hqs : q (Pi.single i.succ 1) = Pi.single i 1 := by
    ext j
    simp [q, Pi.single_apply]
  unfold coordDeriv
  change (fderiv ℝ ((fun y : Space (n + 1) => φ (y 0)) *
    (fun y => ψ (Fin.tail y))) x) _ = _
  rw [(hp.mul hq).fderiv]
  simp [hqs, p, Fin.succ_ne_zero]

/-- No temporal weak derivative is required: a spatial space-time partial
restricts to the corresponding spatial partial on almost every time slice. -/
theorem HasWeakPartialOn.ae_spatial_slices {n : ℕ} {a b : ℝ}
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) [IsFiniteMeasure (volume.restrict Ω)]
    {i : Fin n} {u du : Space (n + 1) → ℝ}
    (hw : HasWeakPartialOn (intervalCylinder a b Ω) i.succ u du)
    (hu : MemLp u 2 (volume.restrict (intervalCylinder a b Ω)))
    (hd : MemLp du 2 (volume.restrict (intervalCylinder a b Ω))) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      HasWeakPartialOn Ω i (fun x => u (Fin.cons t x)) (fun x => du (Fin.cons t x)) := by
  have hμ := cylinderLift_measurePreserving a b hΩ.measurableSet
  apply ae_hasWeakPartialOn_of_product_tests
    (hu.comp_measurePreserving hμ) (hd.comp_measurePreserving hμ)
  intro φ hφ hc hs ψ hψ
  let Φ := fun x : Space (n + 1) => φ (x 0) * ψ (Fin.tail x)
  have hΦ : IsTestFunctionOn (intervalCylinder a b Ω) Φ := cylinder_product_test hφ hc hs hψ
  have hleft := (integrable_mul_of_locallyIntegrableOn hw.locallyIntegrable
    (hΦ.coordDeriv_continuous i.succ) (hΦ.coordDeriv_hasCompactSupport i.succ)
    (hΦ.coordDeriv_tsupport_subset i.succ)).restrict (s := intervalCylinder a b Ω)
  have hright := (integrable_mul_of_locallyIntegrableOn hw.derivative_locallyIntegrable
    hΦ.contDiff.continuous hΦ.hasCompactSupport hΦ.tsupport_subset).restrict
      (s := intervalCylinder a b Ω)
  have hsum : (∫ x in intervalCylinder a b Ω,
      u x * coordDeriv i.succ Φ x + du x * Φ x) = 0 := by
    rw [integral_add hleft hright, hw.integration_by_parts Φ hΦ, neg_add_cancel]
  rw [← integral_cylinderLift a b hΩ.measurableSet] at hsum
  convert hsum using 1
  apply integral_congr_ae
  filter_upwards with z
  rw [coordDeriv_cylinder_product_succ (hφ.differentiable (by simp))
    (hψ.contDiff.differentiable (by simp))]
  simp only [Φ, Fin.cons_zero, Fin.tail_cons, Function.comp_def]
  ring

/-- A finite family of spatial derivatives has one common full-measure time set. -/
theorem ae_all_spatial_weak_partials {n : ℕ} {a b : ℝ}
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) [IsFiniteMeasure (volume.restrict Ω)]
    {u : Space (n + 1) → ℝ} {du : Fin n → Space (n + 1) → ℝ}
    (hu : MemLp u 2 (volume.restrict (intervalCylinder a b Ω)))
    (hd : ∀ i, MemLp (du i) 2 (volume.restrict (intervalCylinder a b Ω)))
    (hw : ∀ i, HasWeakPartialOn (intervalCylinder a b Ω) i.succ u (du i)) :
    ∀ᵐ t ∂volume.restrict (Icc a b), ∀ i,
      HasWeakPartialOn Ω i (fun x => u (Fin.cons t x)) (fun x => du i (Fin.cons t x)) :=
  ae_all_iff.mpr fun i => (hw i).ae_spatial_slices hΩ hu (hd i)

end PDE
