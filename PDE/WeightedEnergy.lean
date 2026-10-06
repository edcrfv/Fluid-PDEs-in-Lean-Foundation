import PDE.WeightedInterpolation
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Measure.Prod

/-! Concrete weighted entropy plus dissipation and its superlinear mixed estimate.
The entropy is a spatial integral and a time essential supremum, not an arbitrary
sequence. Extended values retain possible divergence until finiteness is proved. -/

open MeasureTheory
open scoped ENNReal

namespace PDE

/-- For applications, `f` is the nonnegative entropy cutoff and `d t` is the
spatial integral of its nonnegative dissipations. -/
noncomputable def weightedEnergy {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (ρ f : α × β → ℝ≥0∞) (d : α → ℝ≥0∞) : ℝ≥0∞ :=
  essSup (fun t => ∫⁻ x, ρ (t, x) * f (t, x) ∂ν) μ + ∫⁻ t, d t ∂μ

theorem ae_entropy_le_weightedEnergy
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (ρ f : α × β → ℝ≥0∞) (d : α → ℝ≥0∞) :
    ∀ᵐ t ∂μ, (∫⁻ x, ρ (t, x) * f (t, x) ∂ν) ≤ weightedEnergy μ ν ρ f d := by
  filter_upwards [ENNReal.ae_le_essSup (μ := μ) (fun t => ∫⁻ x, ρ (t, x) * f (t, x) ∂ν)]
    with t ht
  exact ht.trans (le_add_right le_rfl)

theorem lintegral_dissipation_le_weightedEnergy
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (ρ f : α × β → ℝ≥0∞) (d : α → ℝ≥0∞) :
    (∫⁻ t, d t ∂μ) ≤ weightedEnergy μ ν ρ f d :=
  le_add_left le_rfl

/-- Separate bounds for entropy and total dissipation give a bound for their sum.
In an evolution budget each is bounded by the pressure integral, giving a factor two. -/
theorem weightedEnergy_le_of_bounds
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {ρ f : α × β → ℝ≥0∞} {d : α → ℝ≥0∞}
    {E D : ℝ≥0∞} (hE : ∀ᵐ t ∂μ, (∫⁻ x, ρ (t, x) * f (t, x) ∂ν) ≤ E)
    (hD : (∫⁻ t, d t ∂μ) ≤ D) : weightedEnergy μ ν ρ f d ≤ E + D :=
  add_le_add (essSup_le_of_ae_le E hE) hD

/-- Monotonicity is established from the actual cutoffs and dissipations. -/
theorem weightedEnergy_mono
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {ρ f g : α × β → ℝ≥0∞} {d e : α → ℝ≥0∞}
    (hfg : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν, f (t, x) ≤ g (t, x)) (hde : d ≤ᵐ[μ] e) :
    weightedEnergy μ ν ρ f d ≤ weightedEnergy μ ν ρ g e := by
  apply add_le_add _ (lintegral_mono_ae hde)
  refine essSup_mono_ae ?_
  filter_upwards [hfg] with t ht
  exact lintegral_mono_ae (ht.mono fun x hx => mul_le_mul_right hx _)

/-- Pressure retains its physical density while entropy may use a larger storage
weight. In particular `w = ρ+δ` needs no additional p-moment hypothesis. -/
theorem lintegral_weighted_power_le_larger_weight_energy
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {ρ w f : α × β → ℝ≥0∞} {d : α → ℝ≥0∞}
    {p : ℝ} (hp : 3 < p) {A B R L : ℝ≥0∞}
    (hρw : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν, ρ (t, x) ≤ w (t, x))
    (hρ : ∀ᵐ t ∂μ, AEMeasurable (fun x => ρ (t, x)) ν)
    (hf : ∀ᵐ t ∂μ, AEMeasurable (fun x => f (t, x)) ν)
    (hd : AEMeasurable d μ)
    (hR : ∀ᵐ t ∂μ, (∫⁻ x, ρ (t, x) ^ p ∂ν) ≤ R)
    (hS : ∀ᵐ t ∂μ, (∫⁻ x, f (t, x) ^ (6 : ℝ) ∂ν) ^ (1 / 3 : ℝ) ≤
      A * weightedEnergy μ ν w f d ^ 2 + B * d t)
    (hL : weightedEnergy μ ν w f d ≤ L) :
    (∫⁻ z, ρ z ^ (2 : ℝ) * f z ^ (2 + densityInterpolationGain p) ∂μ.prod ν) ≤
      R ^ ((2 - densityInterpolationGain p) / p) * (A * μ Set.univ * L + B) *
        weightedEnergy μ ν w f d ^ (1 + densityInterpolationGain p) := by
  let U := weightedEnergy μ ν w f d
  let r := densityInterpolationGain p
  let s := (2 - r) / p
  have hr : 0 ≤ r := (densityInterpolationGain_pos hp).le
  have hs : 0 ≤ s := by
    have h := densityInterpolationGain_lt_two_thirds hp
    exact div_nonneg (by dsimp [r]; linarith) (by linarith)
  have hpoint : ∀ᵐ t ∂μ,
      (∫⁻ x, ρ (t, x) ^ (2 : ℝ) * f (t, x) ^ (2 + r) ∂ν) ≤
        (U ^ r * R ^ s) * (A * U ^ 2 + B * d t) := by
    filter_upwards [hρw, hρ, hf, hR, hS, ae_entropy_le_weightedEnergy μ ν w f d]
      with t hρwt hρt hft hRt hSt hEt
    have hEt : (∫⁻ x, ρ (t, x) * f (t, x) ∂ν) ≤ U :=
      (lintegral_mono_ae (hρwt.mono fun x hx => mul_le_mul_left hx _)).trans hEt
    calc
      _ ≤ _ := lintegral_density_weighted_interpolation hρt hft hp
      _ ≤ U ^ r * (A * U ^ 2 + B * d t) * R ^ s := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ ∫⁻ t, ∫⁻ x, ρ (t, x) ^ (2 : ℝ) * f (t, x) ^ (2 + r) ∂ν ∂μ :=
      lintegral_prod_le _
    _ ≤ ∫⁻ t, (U ^ r * R ^ s) * (A * U ^ 2 + B * d t) ∂μ :=
      lintegral_mono_ae hpoint
    _ = (U ^ r * R ^ s) * (A * U ^ 2 * μ Set.univ + B * ∫⁻ t, d t ∂μ) := by
      have hmeas : AEMeasurable (fun t => A * U ^ 2 + B * d t) μ :=
        aemeasurable_const.add (aemeasurable_const.mul hd)
      rw [lintegral_const_mul'' _ hmeas,
        lintegral_add_left measurable_const, lintegral_const,
        lintegral_const_mul'' _ hd]
    _ ≤ (U ^ r * R ^ s) * (A * (L * U) * μ Set.univ + B * U) := by
      apply mul_le_mul_right
      apply add_le_add
      · gcongr
        simpa only [pow_two] using mul_le_mul_left hL U
      · exact mul_le_mul_right (lintegral_dissipation_le_weightedEnergy μ ν w f d) B
    _ = R ^ s * (A * μ Set.univ * L + B) * U ^ (1 + r) := by
      rw [ENNReal.rpow_add_of_nonneg 1 r (by norm_num) hr, ENNReal.rpow_one]
      ring

/-- A genuine mixed estimate: a density moment bound, a squared Sobolev estimate,
and a bound on the defined energy imply the power `1 + r > 1`. Here `R` bounds
the p-th density moment, rather than the density norm. Constants are displayed. -/
theorem lintegral_weighted_power_le_energy
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {ρ f : α × β → ℝ≥0∞} {d : α → ℝ≥0∞}
    {p : ℝ} (hp : 3 < p) {A B R L : ℝ≥0∞}
    (hρ : ∀ᵐ t ∂μ, AEMeasurable (fun x => ρ (t, x)) ν)
    (hf : ∀ᵐ t ∂μ, AEMeasurable (fun x => f (t, x)) ν)
    (hd : AEMeasurable d μ)
    (hR : ∀ᵐ t ∂μ, (∫⁻ x, ρ (t, x) ^ p ∂ν) ≤ R)
    (hS : ∀ᵐ t ∂μ, (∫⁻ x, f (t, x) ^ (6 : ℝ) ∂ν) ^ (1 / 3 : ℝ) ≤
      A * weightedEnergy μ ν ρ f d ^ 2 + B * d t)
    (hL : weightedEnergy μ ν ρ f d ≤ L) :
    (∫⁻ z, ρ z ^ (2 : ℝ) * f z ^ (2 + densityInterpolationGain p) ∂μ.prod ν) ≤
      R ^ ((2 - densityInterpolationGain p) / p) * (A * μ Set.univ * L + B) *
        weightedEnergy μ ν ρ f d ^ (1 + densityInterpolationGain p) := by
  exact lintegral_weighted_power_le_larger_weight_energy hp
    (Filter.Eventually.of_forall fun _ => Filter.Eventually.of_forall fun _ => le_rfl)
    hρ hf hd hR hS hL

end PDE
