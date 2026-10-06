import PDE.Galerkin
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Convergent Galerkin approximations

A dense sequence generates nested finite-dimensional trial spaces. Coercivity supplies the
continuous and discrete solutions; Céa's estimate and density prove strong convergence.
This is a stationary variational result. Time-dependent Galerkin ODEs are a later construction.
-/

open Filter Set TopologicalSpace
open scoped Topology
namespace PDE
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Strongly approximating trial vectors imply strong Galerkin convergence by Céa. -/
theorem galerkin_tendsto_of_approximation (S : ℕ → Submodule ℝ V)
    {B : V →L[ℝ] V →L[ℝ] ℝ} {ℓ : V →L[ℝ] ℝ} {α : ℝ} (hα : 0 < α)
    (hcoercive : ∀ v, α * ‖v‖ * ‖v‖ ≤ B v v) {u : V}
    (hu : IsVariationalSolution B ℓ u) (uh w : ℕ → V)
    (hmem : ∀ k, uh k ∈ S k) (huh : ∀ k v, v ∈ S k → B (uh k) v = ℓ v)
    (hw : ∀ k, w k ∈ S k) (hlim : Tendsto w atTop (𝓝 u)) : Tendsto uh atTop (𝓝 u) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
  · intro k
    simpa only [norm_sub_rev] using
      galerkin_error_le (S k) hα hcoercive hu (hmem k) (huh k) (w k) (hw k)
  · simpa only [mul_zero, norm_sub_rev] using
      (tendsto_iff_norm_sub_tendsto_zero.mp hlim).const_mul (‖B‖ / α)

/-- The first k members of a supplied family generate a finite-dimensional trial space. -/
noncomputable def initialTrialSpace (d : ℕ → V) (k : ℕ) : Submodule ℝ V :=
  Submodule.span ℝ (d '' Set.Iio k)

instance initialTrialSpaceFiniteDimensional (d : ℕ → V) (k : ℕ) :
    FiniteDimensional ℝ (initialTrialSpace d k) :=
  FiniteDimensional.span_of_finite ℝ ((Set.finite_Iio k).image d)

theorem initialTrialSpace_mono (d : ℕ → V) : Monotone (initialTrialSpace d) := by
  intro j k hjk
  exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio hjk))

theorem mem_initialTrialSpace (d : ℕ → V) (k : ℕ) : d k ∈ initialTrialSpace d (k + 1) :=
  Submodule.subset_span ⟨k, Nat.lt_succ_self k, rfl⟩

theorem initialTrialSpace_dense (d : ℕ → V) (hd : DenseRange d) :
    Dense (⋃ k, (initialTrialSpace d k : Set V)) := by
  apply hd.mono
  rintro x ⟨k, rfl⟩
  exact mem_iUnion.mpr ⟨k + 1, mem_initialTrialSpace d k⟩

/-- Nested dense trial spaces approximate every point eventually to any prescribed accuracy. -/
theorem eventually_exists_trial_approximation (S : ℕ → Submodule ℝ V) (hS : Monotone S)
    (hd : Dense (⋃ k, (S k : Set V))) (u : V) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ k ≥ N, ∃ v ∈ S k, ‖u - v‖ < ε := by
  obtain ⟨v, hv, hdist⟩ := Metric.mem_closure_iff.mp (hd u) ε hε
  obtain ⟨N, hN⟩ := mem_iUnion.mp hv
  exact ⟨N, fun k hk => ⟨v, hS hk hN, by simpa only [dist_eq_norm] using hdist⟩⟩

/-- Strong Galerkin convergence for nested trial spaces with dense union. -/
theorem galerkin_tendsto_of_dense (S : ℕ → Submodule ℝ V) (hS : Monotone S)
    (hd : Dense (⋃ k, (S k : Set V)))
    {B : V →L[ℝ] V →L[ℝ] ℝ} {ℓ : V →L[ℝ] ℝ} {α : ℝ} (hα : 0 < α)
    (hcoercive : ∀ v, α * ‖v‖ * ‖v‖ ≤ B v v) {u : V}
    (hu : IsVariationalSolution B ℓ u) (uh : ℕ → V)
    (hmem : ∀ k, uh k ∈ S k) (huh : ∀ k v, v ∈ S k → B (uh k) v = ℓ v) :
    Tendsto uh atTop (𝓝 u) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hK : 0 < ‖B‖ / α + 1 := by positivity
  obtain ⟨N, hN⟩ := eventually_exists_trial_approximation S hS hd u (div_pos hε hK)
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨v, hv, herr⟩ := hN k hk
  have hcea := galerkin_error_le (S k) hα hcoercive hu (hmem k) (huh k) v hv
  rw [dist_eq_norm, norm_sub_rev]
  calc
    ‖u - uh k‖ ≤ (‖B‖ / α) * ‖u - v‖ := hcea
    _ ≤ (‖B‖ / α + 1) * ‖u - v‖ := by nlinarith [norm_nonneg (u - v)]
    _ < (‖B‖ / α + 1) * (ε / (‖B‖ / α + 1)) := mul_lt_mul_of_pos_left herr hK
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hK)

/-- Complete Galerkin construction from separability and a coercive bounded form. -/
theorem exists_convergent_galerkin_sequence [CompleteSpace V] [SeparableSpace V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (ℓ : V →L[ℝ] ℝ) :
    ∃ S : ℕ → Submodule ℝ V, (∀ k, FiniteDimensional ℝ (S k)) ∧ Monotone S ∧
      Dense (⋃ k, (S k : Set V)) ∧ ∃ u : V, IsVariationalSolution B ℓ u ∧
        ∃ uh : ℕ → V, (∀ k, uh k ∈ S k) ∧
          (∀ k v, v ∈ S k → B (uh k) v = ℓ v) ∧ Tendsto uh atTop (𝓝 u) := by
  let S := initialTrialSpace (denseSeq V)
  have hmono : Monotone S := initialTrialSpace_mono _
  have hdense : Dense (⋃ k, (S k : Set V)) := initialTrialSpace_dense _ (denseRange_denseSeq V)
  obtain ⟨u, hu, _⟩ := exists_unique_variationalSolution B hB ℓ
  have hdisc (k : ℕ) : ∃ w : S k, ∀ v : S k, B (w : V) (v : V) = ℓ (v : V) :=
    (exists_unique_galerkinSolution (S k) B hB ℓ).exists
  choose uh huh using hdisc
  have htest : ∀ k v, v ∈ S k → B (uh k : V) v = ℓ v := fun k v hv => huh k ⟨v, hv⟩
  refine ⟨S, fun _ => inferInstance, hmono, hdense, u, hu,
    (fun k => (uh k : V)), (fun k => (uh k).property), htest, ?_⟩
  obtain ⟨α, hα, hcoercive⟩ := hB
  exact galerkin_tendsto_of_dense S hmono hdense hα hcoercive hu _
    (fun k => (uh k).property) htest
end PDE
