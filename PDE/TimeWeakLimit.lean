import PDE.TimeLinearTesting

/-!
# Closure of the physical integrated time equation

Joint weak Bochner convergence preserves a linear time equation with a bounded physical
value map, provided the prescribed initial values converge strongly. Scalar spatial tests
separate the vector identity, and all Bochner integrals are justified explicitly.
-/

open InnerProductSpace MeasureTheory Set Filter
open scoped Topology
namespace PDE
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace V] [CompleteSpace H] in
/-- Weighted integrals remain integrable after a bounded map to the physical space. -/
theorem timeL2_weighted_map_integrable {a b : ℝ} (J : V →L[ℝ] H) (u : TimeL2 V a b)
    (g : ℝ → ℝ) (hg : Continuous g) : IntegrableOn (fun t => g t • J (u t)) (Icc a b) := by
  simpa only [map_smul, IntegrableOn] using! J.integrable_comp (timeL2_weighted_integrable u g hg)

omit [CompleteSpace V] in
/-- Scalar spatial tests commute with the actual physical Bochner integral. -/
theorem timeL2_weighted_integral_apply {a b : ℝ} (J : V →L[ℝ] H) (u : TimeL2 V a b)
    (g : ℝ → ℝ) (hg : Continuous g) (ℓ : H →L[ℝ] ℝ) :
    ℓ (∫ t in Icc a b, g t • J (u t)) = ∫ t in Icc a b, g t * (ℓ.comp J) (u t) := by
  rw [← ℓ.integral_comp_comm (timeL2_weighted_map_integrable J u g hg)]
  simp only [map_smul, smul_eq_mul, ContinuousLinearMap.comp_apply]

/-- A physical integrated time equation is closed under joint weak L² convergence and
strong convergence of its prescribed initial values. -/
theorem integrated_time_equation_of_weak_limits {a b : ℝ} (J : V →L[ℝ] H)
    (uN : ℕ → TimeL2 V a b) (dN : ℕ → TimeL2 H a b) (cN : ℕ → H)
    (u : TimeL2 V a b) (d : TimeL2 H a b) (c : H)
    (hu : ∀ z : TimeL2 V a b, Tendsto (fun k => inner ℝ (uN k) z) atTop (𝓝 (inner ℝ u z)))
    (hd : ∀ z : TimeL2 H a b, Tendsto (fun k => inner ℝ (dN k) z) atTop (𝓝 (inner ℝ d z)))
    (hc : Tendsto cN atTop (𝓝 c))
    (hN : ∀ k (η η' : ℝ → ℝ), (∀ t, HasDerivAt η (η' t) t) → Continuous η' → η b = 0 →
      (∫ t in Icc a b, η' t • J (uN k t)) + (∫ t in Icc a b, η t • dN k t) = (-η a) • cN k)
    (η η' : ℝ → ℝ) (hη : ∀ t, HasDerivAt η (η' t) t) (hη' : Continuous η') (hηb : η b = 0) :
    (∫ t in Icc a b, η' t • J (u t)) + (∫ t in Icc a b, η t • d t) = (-η a) • c := by
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun t => (hη t).continuousAt
  apply ext_inner_left ℝ
  intro z
  let ℓ := innerSL ℝ z
  have hi (v : TimeL2 H a b) : ℓ (∫ t in Icc a b, η t • v t) =
      ∫ t in Icc a b, η t * ℓ (v t) := by
    simpa only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply] using
      timeL2_weighted_integral_apply (ContinuousLinearMap.id ℝ H) v η hηc ℓ
  have he (k : ℕ) : (∫ t in Icc a b, η' t * (ℓ.comp J) (uN k t)) +
      (∫ t in Icc a b, η t * ℓ (dN k t)) = (-η a) * ℓ (cN k) := by
    have hh := congrArg ℓ (hN k η η' hη hη' hηb)
    rw [map_add, timeL2_weighted_integral_apply J (uN k) η' hη' ℓ, hi,
      map_smul, smul_eq_mul] at hh
    exact hh
  have ha := timeL2_weighted_clm_tendsto η' hη' (ℓ.comp J) uN u hu
  have hb := timeL2_weighted_clm_tendsto η hηc ℓ dN d hd
  have hci := (ℓ.continuous.continuousAt.tendsto.comp hc).const_mul (-η a)
  have hlim := tendsto_nhds_unique (ha.add hb)
    (hci.congr' (Filter.EventuallyEq.symm (Eventually.of_forall he)))
  change ℓ ((∫ t in Icc a b, η' t • J (u t)) + (∫ t in Icc a b, η t • d t)) = ℓ ((-η a) • c)
  rw [map_add, timeL2_weighted_integral_apply J u η' hη' ℓ, hi, map_smul, smul_eq_mul]
  exact hlim
end PDE
