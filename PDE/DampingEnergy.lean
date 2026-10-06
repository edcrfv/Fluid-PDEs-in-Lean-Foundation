import PDE.WeightedEnergy

/-! Cubic thermal damping produces an unweighted low-temperature source. The
artificial storage weight `r ≥ δ` controls that source uniformly for `δ ≤ 1`.
These estimates retain extended integrals, including possible infinite values. -/

open MeasureTheory
open scoped ENNReal

namespace PDE

/-- Three-factor Hölder with weights `q`, `1/3`, `2/3-q`. The coefficient has
no inverse power of `δ`, and the physical density may vanish. -/
theorem lintegral_damping_interpolation
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {r f : α → ℝ≥0∞}
    {δ : ℝ≥0∞} (hδ : δ ≤ 1) (hr : ∀ᵐ x ∂μ, δ ≤ r x)
    (hrm : AEMeasurable r μ) (hf : AEMeasurable f μ)
    {q : ℝ} (hq : 0 ≤ q) (hqmax : q ≤ 2 / 3) :
    (∫⁻ x, δ * f x ^ (2 + q) ∂μ) ≤
      μ Set.univ ^ (2 / 3 - q) * (∫⁻ x, r x * f x ∂μ) ^ q *
        (∫⁻ x, f x ^ (6 : ℝ) ∂μ) ^ (1 / 3 : ℝ) := by
  let F : Fin 3 → α → ℝ≥0∞ := ![fun x => r x * f x,
    fun x => f x ^ (6 : ℝ), fun _ => 1]
  let w : Fin 3 → ℝ := ![q, 1 / 3, 2 / 3 - q]
  have hF : ∀ i ∈ Finset.univ, AEMeasurable (F i) μ := by
    intro i _
    fin_cases i
    · exact hrm.mul hf
    · exact hf.pow_const _
    · exact aemeasurable_const
  have hw : ∑ i ∈ Finset.univ, w i = 1 := by
    simp [w, Fin.sum_univ_succ]
    ring
  have hw0 : ∀ i ∈ Finset.univ, 0 ≤ w i := by
    intro i _
    fin_cases i
    · exact hq
    · norm_num [w]
    · exact sub_nonneg.mpr hqmax
  have h := ENNReal.lintegral_prod_norm_pow_le Finset.univ hF hw hw0
  simp only [F, w, Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.prod_univ_zero, mul_one, ENNReal.one_rpow, lintegral_one] at h
  have hδq : δ ≤ δ ^ q := by
    simpa using ENNReal.rpow_le_rpow_of_exponent_ge hδ (show q ≤ 1 by linarith)
  calc
    _ ≤ ∫⁻ x, (r x * f x) ^ q * (f x ^ (6 : ℝ)) ^ (1 / 3 : ℝ) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hr] with x hx
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq, ← ENNReal.rpow_mul,
        show (6 : ℝ) * (1 / 3) = 2 by norm_num,
        ENNReal.rpow_add_of_nonneg 2 q (by norm_num) hq]
      calc
        _ ≤ r x ^ q * (f x ^ (2 : ℝ) * f x ^ q) :=
          mul_le_mul_left (hδq.trans (ENNReal.rpow_le_rpow hx hq)) _
        _ = _ := by ring
    _ ≤ _ := by simpa only [mul_comm, mul_left_comm, mul_assoc] using h

/-- The artificial damping source has the same superlinear energy exponent as
the pressure estimate. `r` will be `ρ+δ`; the displayed squared Sobolev bound
and the bound `L` still have to be supplied from the actual cutoff and budget. -/
theorem lintegral_damping_power_le_energy
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {r f : α × β → ℝ≥0∞} {d : α → ℝ≥0∞}
    {δ : ℝ≥0∞} (hδ : δ ≤ 1) (hr : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν, δ ≤ r (t, x))
    (hrm : ∀ᵐ t ∂μ, AEMeasurable (fun x => r (t, x)) ν)
    (hf : ∀ᵐ t ∂μ, AEMeasurable (fun x => f (t, x)) ν)
    (hd : AEMeasurable d μ) {q : ℝ} (hq : 0 ≤ q) (hqmax : q ≤ 2 / 3)
    {A B L : ℝ≥0∞}
    (hS : ∀ᵐ t ∂μ, (∫⁻ x, f (t, x) ^ (6 : ℝ) ∂ν) ^ (1 / 3 : ℝ) ≤
      A * weightedEnergy μ ν r f d ^ 2 + B * d t)
    (hL : weightedEnergy μ ν r f d ≤ L) :
    (∫⁻ z, δ * f z ^ (2 + q) ∂μ.prod ν) ≤
      ν Set.univ ^ (2 / 3 - q) * (A * μ Set.univ * L + B) *
        weightedEnergy μ ν r f d ^ (1 + q) := by
  let U := weightedEnergy μ ν r f d
  let V := ν Set.univ ^ (2 / 3 - q)
  have hpoint : ∀ᵐ t ∂μ, (∫⁻ x, δ * f (t, x) ^ (2 + q) ∂ν) ≤
      (V * U ^ q) * (A * U ^ 2 + B * d t) := by
    filter_upwards [hr, hrm, hf, hS, ae_entropy_le_weightedEnergy μ ν r f d]
      with t hrt hrmt hft hSt hEt
    exact (lintegral_damping_interpolation hδ hrt hrmt hft hq hqmax).trans
      (by gcongr)
  calc
    _ ≤ ∫⁻ t, ∫⁻ x, δ * f (t, x) ^ (2 + q) ∂ν ∂μ := lintegral_prod_le _
    _ ≤ ∫⁻ t, (V * U ^ q) * (A * U ^ 2 + B * d t) ∂μ := lintegral_mono_ae hpoint
    _ = (V * U ^ q) * (A * U ^ 2 * μ Set.univ + B * ∫⁻ t, d t ∂μ) := by
      have hmeas : AEMeasurable (fun t => A * U ^ 2 + B * d t) μ :=
        aemeasurable_const.add (aemeasurable_const.mul hd)
      rw [lintegral_const_mul'' _ hmeas, lintegral_add_left measurable_const,
        lintegral_const, lintegral_const_mul'' _ hd]
    _ ≤ (V * U ^ q) * (A * (L * U) * μ Set.univ + B * U) := by
      apply mul_le_mul_right
      apply add_le_add
      · gcongr
        simpa only [pow_two] using mul_le_mul_left hL U
      · exact mul_le_mul_right (lintegral_dissipation_le_weightedEnergy μ ν r f d) B
    _ = _ := by
      rw [ENNReal.rpow_add_of_nonneg 1 q (by norm_num) hq, ENNReal.rpow_one]
      ring

end PDE
