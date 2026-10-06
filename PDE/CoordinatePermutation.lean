import PDE.SobolevSlicing

/-! Coordinate permutations preserve actual distributional weak derivatives.
All changes of variables use restricted Lebesgue measure. -/

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace PDE

/-- Reindex spatial coordinates; the inverse permutation acts on basis vectors. -/
def permuteCoordinates {n : ℕ} (e : Equiv.Perm (Fin n)) : Space n ≃L[ℝ] Space n :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n => ℝ) e.symm

@[simp] theorem permuteCoordinates_apply {n : ℕ} (e : Equiv.Perm (Fin n)) (x : Space n)
    (i : Fin n) : permuteCoordinates e x i = x (e i) := by
  simp [permuteCoordinates, ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft]

@[simp] theorem permuteCoordinates_inverse {n : ℕ} (e : Equiv.Perm (Fin n)) (x : Space n) :
    permuteCoordinates e.symm (permuteCoordinates e x) = x := by ext i; simp

@[simp] theorem permuteCoordinates_update {n : ℕ} (e : Equiv.Perm (Fin n))
    (x : Space n) (i : Fin n) (t : ℝ) :
    permuteCoordinates e (Function.update x i t) =
      Function.update (permuteCoordinates e x) (e.symm i) t := by
  ext j
  simp [Function.update_apply, Equiv.eq_symm_apply]

theorem permuteCoordinates_measurePreserving {n : ℕ} (e : Equiv.Perm (Fin n))
    {Ω : Set (Space n)} (hΩ : MeasurableSet Ω) :
    MeasurePreserving (permuteCoordinates e)
      (volume.restrict (permuteCoordinates e ⁻¹' Ω)) (volume.restrict Ω) :=
  (volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) e.symm).restrict_preimage hΩ

theorem coordDeriv_permuteCoordinates {n : ℕ} (e : Equiv.Perm (Fin n))
    {φ : Space n → ℝ} (hφ : Differentiable ℝ φ) (i : Fin n) (x : Space n) :
    coordDeriv i (fun y => φ (permuteCoordinates e y)) x =
      coordDeriv (e.symm i) φ (permuteCoordinates e x) := by
  have hd := (hφ (permuteCoordinates e x)).hasFDerivAt.comp x
    (permuteCoordinates e).hasFDerivAt
  change ((fderiv ℝ (φ ∘ permuteCoordinates e)) x) _ = _
  rw [hd.fderiv]
  have he : permuteCoordinates e (Pi.single i 1) = Pi.single (e.symm i) 1 := by
    ext j
    simp [Pi.single_apply, Equiv.eq_symm_apply]
  change (fderiv ℝ φ (permuteCoordinates e x)) (permuteCoordinates e (Pi.single i 1)) = _
  rw [he]
  rfl

/-- L² weak derivatives transport with the coordinate index. This proves the
distributional identity against all compact smooth tests on the pulled-back domain. -/
theorem HasWeakPartialOn.permuteCoordinates {n : ℕ} {Ω : Set (Space n)}
    (hΩ : MeasurableSet Ω) {i : Fin n} {u du : Space n → ℝ}
    (hw : HasWeakPartialOn Ω i u du)
    (hu : MemLp u 2 (volume.restrict Ω)) (hd : MemLp du 2 (volume.restrict Ω))
    (e : Equiv.Perm (Fin n)) :
    HasWeakPartialOn (PDE.permuteCoordinates e ⁻¹' Ω) (e i)
      (fun x => u (PDE.permuteCoordinates e x)) (fun x => du (PDE.permuteCoordinates e x)) := by
  have hμ := permuteCoordinates_measurePreserving e hΩ
  refine ⟨locallyIntegrableOn_of_locallyIntegrable_restrict
    ((hu.comp_measurePreserving hμ).locallyIntegrable (by norm_num)),
    locallyIntegrableOn_of_locallyIntegrable_restrict
    ((hd.comp_measurePreserving hμ).locallyIntegrable (by norm_num)), ?_⟩
  intro φ hφ
  let Φ := fun x => φ (PDE.permuteCoordinates e.symm x)
  have hΦ : IsTestFunctionOn Ω Φ := by
    refine ⟨hφ.contDiff.comp (PDE.permuteCoordinates e.symm).contDiff,
      hφ.hasCompactSupport.comp_homeomorph (PDE.permuteCoordinates e.symm).toHomeomorph, ?_⟩
    intro x hx
    have ht : PDE.permuteCoordinates e.symm x ∈ tsupport φ :=
      (Set.ext_iff.mp (tsupport_comp_eq_preimage φ
        (PDE.permuteCoordinates e.symm).toHomeomorph) x).mp hx
    have h := hφ.tsupport_subset ht
    have he : PDE.permuteCoordinates e (PDE.permuteCoordinates e.symm x) = x := by
      ext j
      simp
    change PDE.permuteCoordinates e (PDE.permuteCoordinates e.symm x) ∈ Ω at h
    rwa [he] at h
  have hid := hw.integration_by_parts Φ hΦ
  have hder (x : Space n) : coordDeriv i Φ (PDE.permuteCoordinates e x) =
      coordDeriv (e i) φ x := by
    simpa only [Φ, Equiv.symm_symm, permuteCoordinates_inverse] using
      coordDeriv_permuteCoordinates e.symm (hφ.contDiff.differentiable (by simp)) i
        (PDE.permuteCoordinates e x)
  have hl := hμ.integral_comp (PDE.permuteCoordinates e).toHomeomorph.measurableEmbedding
    (fun x => u x * coordDeriv i Φ x)
  have hr := hμ.integral_comp (PDE.permuteCoordinates e).toHomeomorph.measurableEmbedding
    (fun x => du x * Φ x)
  rw [← hl, ← hr] at hid
  simpa only [hder, Φ, permuteCoordinates_inverse] using hid

end PDE
