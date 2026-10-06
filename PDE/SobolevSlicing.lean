import PDE.ProductWeakSlicing
import PDE.SobolevInterval

/-!
# Coordinate slices of the actual distributional H¹ graph

On an open cylinder, the first distributional partial derivative gives weak
interval derivatives on almost every transverse slice. In particular, each
such slice has an AC representative with the prescribed derivative. No ACL
regularity is assumed, and no simultaneous pointwise cylinder representative
is asserted.
-/

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace PDE

/-- An interval in the first coordinate, with an arbitrary transverse domain. -/
def intervalCylinder {n : ℕ} (a b : ℝ) (Ω : Set (Space n)) : Set (Space (n + 1)) :=
  {x | x 0 ∈ Ioo a b ∧ Fin.tail x ∈ Ω}

theorem isOpen_intervalCylinder {n : ℕ} (a b : ℝ) {Ω : Set (Space n)} (hΩ : IsOpen Ω) :
    IsOpen (intervalCylinder a b Ω) :=
  (isOpen_Ioo.preimage (continuous_apply 0)).inter (hΩ.preimage (by fun_prop))

/-- The usual coordinate parametrization transports the actual restricted
Lebesgue measures; interval endpoints do not affect this statement. -/
theorem cylinderLift_measurePreserving {n : ℕ} (a b : ℝ)
    {Ω : Set (Space n)} (hΩ : MeasurableSet Ω) :
    MeasurePreserving (fun z : ℝ × Space n => Fin.cons z.1 z.2)
      ((volume.restrict (Icc a b)).prod (volume.restrict Ω))
      (volume.restrict (intervalCylinder a b Ω)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).restrict_preimage
    (s := Ioo a b ×ˢ Ω) (measurableSet_Ioo.prod hΩ)
  have he : e ⁻¹' (Ioo a b ×ˢ Ω) = intervalCylinder a b Ω := by
    ext x
    simp [e, MeasurableEquiv.piFinSuccAbove, intervalCylinder]
  rw [he] at h
  have hi := MeasurePreserving.symm e h
  have heinv : (fun z : ℝ × Space n => Fin.cons z.1 z.2) = e.symm := by
    funext z
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    change Fin.cons z.1 z.2 = @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) 0 z.1 z.2
    exact (Fin.insertNth_zero' z.1 z.2).symm
  change MeasurePreserving e.symm ((volume.prod volume).restrict (Ioo a b ×ˢ Ω)) _ at hi
  rw [← Measure.prod_restrict, Measure.restrict_congr_set Ioo_ae_eq_Icc] at hi
  rwa [heinv]

theorem integral_cylinderLift {n : ℕ} (a b : ℝ)
    {Ω : Set (Space n)} (hΩ : MeasurableSet Ω) (f : Space (n + 1) → ℝ) :
    (∫ z, f (Fin.cons z.1 z.2) ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
      ∫ x in intervalCylinder a b Ω, f x := by
  apply (cylinderLift_measurePreserving a b hΩ).integral_comp
  exact (Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)).toHomeomorph.measurableEmbedding

/-- A separated time-space test is a genuine compact smooth cylinder test. -/
theorem cylinder_product_test {n : ℕ} {a b : ℝ} {Ω : Set (Space n)}
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo a b) {ψ : Space n → ℝ} (hψ : IsTestFunctionOn Ω ψ) :
    IsTestFunctionOn (intervalCylinder a b Ω) (fun x => φ (x 0) * ψ (Fin.tail x)) := by
  let e := (Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)).symm.toHomeomorph
  let f := fun z : ℝ × Space n => φ z.1 * ψ z.2
  have hsupport : tsupport f ⊆ tsupport φ ×ˢ tsupport ψ := by
    apply closure_minimal _ (isClosed_tsupport φ |>.prod (isClosed_tsupport ψ))
    intro z hz
    have hn : φ z.1 ≠ 0 ∧ ψ z.2 ≠ 0 := mul_ne_zero_iff.mp hz
    exact ⟨subset_tsupport φ hn.1, subset_tsupport ψ hn.2⟩
  have hcompact : HasCompactSupport f :=
    (hc.isCompact.prod hψ.hasCompactSupport.isCompact).of_isClosed_subset
      (isClosed_tsupport f) hsupport
  have htail : ContDiff ℝ ∞ (Fin.tail : Space (n + 1) → Space n) := by
    change ContDiff ℝ ∞ (fun (x : Space (n + 1)) (j : Fin n) => x j.succ)
    fun_prop
  refine ⟨(hφ.comp (by fun_prop)).mul (hψ.contDiff.comp htail),
    hcompact.comp_homeomorph e, ?_⟩
  intro x hx
  have hx' : e x ∈ tsupport f := by
    exact (Set.ext_iff.mp (tsupport_comp_eq_preimage f e) x).mp hx
  exact ⟨hs (hsupport hx').1, hψ.tsupport_subset (hsupport hx').2⟩

private theorem coordDeriv_cylinder_product {n : ℕ}
    {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) {ψ : Space n → ℝ}
    (hψ : Differentiable ℝ ψ) (x : Space (n + 1)) :
    coordDeriv 0 (fun y => φ (y 0) * ψ (Fin.tail y)) x =
      deriv φ (x 0) * ψ (Fin.tail x) := by
  let p : Space (n + 1) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let q : Space (n + 1) →L[ℝ] Space n :=
    ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj j.succ)
  have hp : HasFDerivAt (fun y => φ (y 0)) (deriv φ (x 0) • p) x :=
    (hφ (x 0)).hasDerivAt.comp_hasFDerivAt x p.hasFDerivAt
  have hq : HasFDerivAt (fun y => ψ (Fin.tail y)) ((fderiv ℝ ψ (Fin.tail x)).comp q) x :=
    (hψ (Fin.tail x)).hasFDerivAt.comp x q.hasFDerivAt
  unfold coordDeriv
  change (fderiv ℝ ((fun y : Space (n + 1) => φ (y 0)) *
    (fun y => ψ (Fin.tail y))) x) _ = _
  rw [(hp.mul hq).fderiv]
  have hqzero : q (Pi.single (0 : Fin (n + 1)) 1) = 0 := by
    ext j
    simp [q, Fin.succ_ne_zero]
  simp [hqzero, p, mul_comm]

/-- A genuine distributional first partial derivative restricts to a weak
interval derivative on almost every transverse line. The cylinder need not
have zero boundary values. -/
theorem HasWeakPartialOn.ae_interval_slices {n : ℕ} {a b : ℝ}
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) [IsFiniteMeasure (volume.restrict Ω)]
    {u du : Space (n + 1) → ℝ}
    (hw : HasWeakPartialOn (intervalCylinder a b Ω) 0 u du)
    (hu : MemLp u 2 (volume.restrict (intervalCylinder a b Ω)))
    (hd : MemLp du 2 (volume.restrict (intervalCylinder a b Ω))) :
    ∀ᵐ y ∂volume.restrict Ω,
      HasWeakDerivativeOnInterval a b (fun t => u (Fin.cons t y)) (fun t => du (Fin.cons t y)) := by
  have hμ := cylinderLift_measurePreserving a b hΩ.measurableSet
  apply ae_hasWeakDerivativeOnInterval_of_product_tests hΩ
    (hu.comp_measurePreserving hμ) (hd.comp_measurePreserving hμ)
  intro φ hφ hc hs ψ hψ
  let Φ := fun x : Space (n + 1) => φ (x 0) * ψ (Fin.tail x)
  have hΦ : IsTestFunctionOn (intervalCylinder a b Ω) Φ := cylinder_product_test hφ hc hs hψ
  have hleft := (integrable_mul_of_locallyIntegrableOn hw.locallyIntegrable
    (hΦ.coordDeriv_continuous 0) (hΦ.coordDeriv_hasCompactSupport 0)
    (hΦ.coordDeriv_tsupport_subset 0)).restrict (s := intervalCylinder a b Ω)
  have hright := (integrable_mul_of_locallyIntegrableOn hw.derivative_locallyIntegrable
    hΦ.contDiff.continuous hΦ.hasCompactSupport hΦ.tsupport_subset).restrict
      (s := intervalCylinder a b Ω)
  have hsum : (∫ x in intervalCylinder a b Ω, u x * coordDeriv 0 Φ x + du x * Φ x) = 0 := by
    rw [integral_add hleft hright, hw.integration_by_parts Φ hΦ, neg_add_cancel]
  rw [← integral_cylinderLift a b hΩ.measurableSet] at hsum
  convert hsum using 1
  apply integral_congr_ae
  filter_upwards with z
  change ψ z.2 * (deriv φ z.1 * u (Fin.cons z.1 z.2) + φ z.1 * du (Fin.cons z.1 z.2)) = _
  rw [coordDeriv_cylinder_product (hφ.differentiable (by simp)) (hψ.contDiff.differentiable (by simp))]
  simp only [Φ, Fin.cons_zero, Fin.tail_cons]
  ring

/-- Actual H¹ weak partials, rather than an ACL hypothesis, supply AC line
representatives and their a.e. derivatives. Representatives are chosen per line. -/
theorem H1.ae_interval_AC_representative {n : ℕ} {a b : ℝ} (hab : a < b)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) [IsFiniteMeasure (volume.restrict Ω)]
    (u : H1 (intervalCylinder a b Ω)) :
    ∀ᵐ y ∂volume.restrict Ω, ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v a b ∧
      (fun t => H1.value (intervalCylinder a b Ω) u (Fin.cons t y)) =ᵐ[volume.restrict (Icc a b)] v ∧
      deriv v =ᵐ[volume.restrict (Icc a b)]
        (fun t => H1.derivative (intervalCylinder a b Ω) 0 u (Fin.cons t y)) :=
  ((u.hasWeakPartialOn 0).ae_interval_slices hΩ (Lp.memLp _) (Lp.memLp _)).mono
    fun _ hy => hy.exists_absolutelyContinuous_representative hab

/-- Geometric mean Poincaré holds on almost every first-coordinate slice of
the actual H¹ class, using its actual weak derivative and the interval length. -/
theorem H1.ae_interval_mean_poincare {n : ℕ} {a b : ℝ} (hab : a < b)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) [IsFiniteMeasure (volume.restrict Ω)]
    (u : H1 (intervalCylinder a b Ω)) :
    ∀ᵐ y ∂volume.restrict Ω,
      (∫ t in Icc a b, (H1.value (intervalCylinder a b Ω) u (Fin.cons t y) -
        (∫ s in Icc a b, H1.value (intervalCylinder a b Ω) u (Fin.cons s y)) / (b - a)) ^ 2) ≤
      (b - a) ^ 2 * ∫ t in Icc a b, H1.derivative (intervalCylinder a b Ω) 0 u (Fin.cons t y) ^ 2 := by
  have hμ := cylinderLift_measurePreserving a b hΩ.measurableSet
  have hv := (Lp.memLp (H1.value (intervalCylinder a b Ω) u)).comp_measurePreserving hμ
  have hd := (Lp.memLp (H1.derivative (intervalCylinder a b Ω) 0 u)).comp_measurePreserving hμ
  filter_upwards [(u.hasWeakPartialOn 0).ae_interval_slices hΩ (Lp.memLp _) (Lp.memLp _),
    hv.aestronglyMeasurable.prodMk_right, hv.integrable_sq.prod_left_ae,
    hd.aestronglyMeasurable.prodMk_right, hd.integrable_sq.prod_left_ae]
    with y hy hym hyi hdm hdi
  exact hy.mean_poincare hab ((memLp_two_iff_integrable_sq hym).mpr hyi)
    ((memLp_two_iff_integrable_sq hdm).mpr hdi)

end PDE
