import PDE.MassForm

/-!
# Physical orthogonal projection to finite trial spaces

The mass operator projects arbitrary physical-space initial data to trial vectors.
The projected physical norm is at most the initial norm, and the error is no larger
than that of any trial vector. These estimates have constant 1 in every dimension.
-/

open InnerProductSpace
namespace PDE
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Physical orthogonal projection, expressed as a vector in the finite-dimensional trial space. -/
noncomputable def massProjection (J : V →L[ℝ] H) (hJ : Function.Injective J) (f : H) : V :=
  (massForm_isCoercive J hJ).continuousLinearEquivOfBilin.symm
    ((toDual ℝ V).symm ((innerSL ℝ f).comp J))

theorem massProjection_spec (J : V →L[ℝ] H) (hJ : Function.Injective J) (f : H) (v : V) :
    inner ℝ (J (massProjection J hJ f)) (J v) = inner ℝ f (J v) := by
  change massForm J (massProjection J hJ f) v = _
  rw [← (massForm_isCoercive J hJ).continuousLinearEquivOfBilin_apply]
  unfold massProjection
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact toDual_symm_apply

theorem massProjection_norm_le (J : V →L[ℝ] H) (hJ : Function.Injective J) (f : H) :
    ‖J (massProjection J hJ f)‖ ≤ ‖f‖ := by
  have h := massProjection_spec J hJ f (massProjection J hJ f)
  rw [real_inner_self_eq_norm_sq] at h
  have hb := real_inner_le_norm f (J (massProjection J hJ f))
  nlinarith [norm_nonneg f, norm_nonneg (J (massProjection J hJ f))]

theorem massProjection_orthogonal (J : V →L[ℝ] H) (hJ : Function.Injective J) (f : H) (v : V) :
    inner ℝ (f - J (massProjection J hJ f)) (J v) = 0 := by
  rw [inner_sub_left, massProjection_spec, sub_self]

/-- Best approximation in the physical Hilbert norm, with constant 1. -/
theorem massProjection_bestApproximation (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (f : H) (v : V) : ‖f - J (massProjection J hJ f)‖ ≤ ‖f - J v‖ := by
  have horth : inner ℝ (f - J (massProjection J hJ f)) (J (massProjection J hJ f) - J v) = 0 := by
    rw [← map_sub]
    exact massProjection_orthogonal J hJ f _
  have hs := norm_add_sq_real (f - J (massProjection J hJ f)) (J (massProjection J hJ f) - J v)
  rw [sub_add_sub_cancel, horth] at hs
  nlinarith [norm_nonneg (f - J (massProjection J hJ f)), norm_nonneg (f - J v),
    sq_nonneg ‖J (massProjection J hJ f) - J v‖]
end PDE
