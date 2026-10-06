import PDE.WeakDerivativeLimit
import PDE.SobolevCompactness
import PDE.WeakEnergyBudget

/-! Compactness of a selected family of weak partial derivatives. For a
space-time domain one may select only spatial coordinates. A single subsequence
works for all selected derivatives; the limiting value is identified by its
bounded a.e. limit. -/

open MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace PDE

/-- Bounded derivative energy constructs actual weak derivatives of a bounded
a.e. limit. The space-time version does not assert a time derivative. -/
theorem exists_weak_partials_of_bounded_energy
    {n m : ℕ} {Ω : Set (Space n)} [IsFiniteMeasure (volume.restrict Ω)]
    (coord : Fin m → Fin n) {f : ℕ → Space n → ℝ} {g : Space n → ℝ}
    (d : ℕ → Fin m → DomainL2 Ω) {K B : ℝ}
    (hf : ∀ j, AEStronglyMeasurable (f j) (volume.restrict Ω))
    (hg : AEStronglyMeasurable g (volume.restrict Ω))
    (hfK : ∀ j, ∀ᵐ x ∂volume.restrict Ω, ‖f j x‖ ≤ K)
    (hgK : ∀ᵐ x ∂volume.restrict Ω, ‖g x‖ ≤ K)
    (hfg : ∀ᵐ x ∂volume.restrict Ω, Tendsto (fun j => f j x) atTop (𝓝 (g x)))
    (hB : 0 ≤ B) (hb : ∀ j, ∑ i, ‖d j i‖ ^ 2 ≤ B)
    (hw : ∀ j i, HasWeakPartialOn Ω (coord i) (f j) (d j i)) :
    ∃ v : Fin m → DomainL2 Ω, (∀ i, HasWeakPartialOn Ω (coord i) g (v i)) ∧
      ∃ r : ℕ → ℕ, StrictMono r ∧ ∀ i w,
        Tendsto (fun j => inner ℝ (d (r j) i) w) atTop (𝓝 (inner ℝ (v i) w)) := by
  let U (j : ℕ) : PiLp 2 (fun _ : Fin m => DomainL2 Ω) := WithLp.toLp 2 (d j)
  have hnorm (j : ℕ) : ‖U j‖ ≤ Real.sqrt B := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hB, PiLp.norm_sq_eq_of_L2]
    exact hb j
  obtain ⟨v, _, r, hr, hlim⟩ := exists_weakly_convergent_subsequence U hnorm
  have hcoords (i : Fin m) (w : DomainL2 Ω) :
      Tendsto (fun j => inner ℝ (d (r j) i) w) atTop (𝓝 (inner ℝ (v i) w)) := by
    let L : PiLp 2 (fun _ : Fin m => DomainL2 Ω) →L[ℝ] ℝ :=
      (innerSL ℝ w).comp (PiLp.proj 2 _ i)
    have ht := hlim ((toDual ℝ _).symm L)
    have he (z : PiLp 2 (fun _ : Fin m => DomainL2 Ω)) :
        inner ℝ z ((toDual ℝ _).symm L) = inner ℝ (z i) w := by
      rw [real_inner_comm, toDual_symm_apply]
      change inner ℝ w (z i) = inner ℝ (z i) w
      exact real_inner_comm _ _
    simpa only [he] using ht
  refine ⟨fun i => v i, ?_, r, hr, hcoords⟩
  intro i
  exact HasWeakPartialOn.of_bounded_ae_of_weak_L2
    (fun j => hf (r j)) hg (fun j => hfK (r j)) hgK
    (hfg.mono fun _ hx => hx.comp hr.tendsto_atTop) (hcoords i)
    (fun j => hw (r j) i)

/-- A convergent energy budget constructs the limiting derivatives as well as
their budget. No derivative limit or separate uniform energy constant is an input. -/
theorem exists_weak_partials_and_energy_budget
    {n m : ℕ} {Ω : Set (Space n)} [IsFiniteMeasure (volume.restrict Ω)]
    (coord : Fin m → Fin n) {f : ℕ → Space n → ℝ} {g : Space n → ℝ}
    (d : ℕ → Fin m → DomainL2 Ω) {K k : ℝ} {F S : ℕ → ℝ} {F₀ S₀ : ℝ}
    (hf : ∀ j, AEStronglyMeasurable (f j) (volume.restrict Ω))
    (hg : AEStronglyMeasurable g (volume.restrict Ω))
    (hfK : ∀ j, ∀ᵐ x ∂volume.restrict Ω, ‖f j x‖ ≤ K)
    (hgK : ∀ᵐ x ∂volume.restrict Ω, ‖g x‖ ≤ K)
    (hfg : ∀ᵐ x ∂volume.restrict Ω, Tendsto (fun j => f j x) atTop (𝓝 (g x)))
    (hk : 0 < k) (hF0 : ∀ j, 0 ≤ F j)
    (hF : Tendsto F atTop (𝓝 F₀)) (hS : Tendsto S atTop (𝓝 S₀))
    (hw : ∀ j i, HasWeakPartialOn Ω (coord i) (f j) (d j i))
    (hb : ∀ j, F j + k * ∑ i, ‖d j i‖ ^ 2 ≤ S j) :
    ∃ v : Fin m → DomainL2 Ω, (∀ i, HasWeakPartialOn Ω (coord i) g (v i)) ∧
      F₀ + k * ∑ i, ‖v i‖ ^ 2 ≤ S₀ := by
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ hS).bddAbove
  have henergy (j : ℕ) : ∑ i, ‖d j i‖ ^ 2 ≤ max B 0 / k := by
    apply (le_div_iff₀ hk).mpr
    have hs := hB (Set.mem_range_self j)
    have hh := hb j
    have hmax := le_max_left B 0
    have hnonneg := hF0 j
    nlinarith
  obtain ⟨v, hv, r, hr, hweak⟩ := exists_weak_partials_of_bounded_energy coord d
    hf hg hfK hgK hfg (div_nonneg (le_max_right B 0) hk.le) henergy hw
  exact ⟨v, hv, energy_budget_of_weak_limit_finite hk.le (fun i => hweak i (v i))
    (hF.comp hr.tendsto_atTop) (hS.comp hr.tendsto_atTop) (fun j => hb (r j))⟩

end PDE
