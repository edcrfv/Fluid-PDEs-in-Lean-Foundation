import PDE.CompressionInterpolation
import PDE.CubeDensityEnergy

/-! Compression work is subcritical in the actual density gradient energy for
every p>3. Constants are chosen before the fields, and vacuum is permitted. -/

open MeasureTheory
open scoped ENNReal

namespace PDE

theorem exists_cube_compression_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {p R₂ R D : ℝ} (hp : 3 < p) (hR₂ : 0 ≤ R₂) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    ∃ K r : ℝ, 0 ≤ K ∧ 0 ≤ r ∧ r < 1 / 2 ∧
      ∀ (ρ d : α × Space 3 → ℝ) (du : Fin 3 → α × Space 3 → ℝ),
        Measurable ρ → Measurable d →
        MemLp ρ 2 (μ.prod (volume.restrict (unitOpenCube 3))) →
        (∀ i, MemLp (du i) 2 (μ.prod (volume.restrict (unitOpenCube 3)))) →
        (∀ᵐ t ∂μ, ∀ i, HasWeakPartialOn (unitOpenCube 3) i (fun x => ρ (t, x)) (fun x => du i (t, x))) →
        (∀ᵐ t ∂μ, lpNorm (fun x => ρ (t, x)) 2 (volume.restrict (unitOpenCube 3)) ≤ R₂) →
        (∀ᵐ t ∂μ, (∫⁻ x in unitOpenCube 3, ENNReal.ofReal |ρ (t, x)| ^ p) ≤ ENNReal.ofReal R) →
        (∫⁻ z, ENNReal.ofReal |d z| ^ (2 : ℝ) ∂μ.prod (volume.restrict (unitOpenCube 3))) ≤ ENNReal.ofReal D →
        Integrable (fun z => |ρ z ^ 2 * d z|) (μ.prod (volume.restrict (unitOpenCube 3))) ∧
        (∫ z, |ρ z ^ 2 * d z| ∂μ.prod (volume.restrict (unitOpenCube 3))) ≤
          K * (1 + ∫ z, ∑ i, du i z ^ 2 ∂μ.prod (volume.restrict (unitOpenCube 3))) ^ r := by
  let p₀ := min p 4
  have hp₀ : 3 < p₀ := lt_min hp (by norm_num)
  obtain ⟨hb, hq, hq1, hsum, hexp⟩ := compression_interpolation_exponents hp₀ (min_le_right _ _)
  let b := 2 / (6 - p₀)
  let q := 3 * (4 - p₀) / (6 - p₀)
  let S := 2 * R₂ ^ 2 * (μ Set.univ).toReal + 288
  let K := (1 + R) ^ (b / 2) * S ^ (q / 2) * D ^ (1 / 2 : ℝ) *
    (μ Set.univ).toReal ^ ((1 - q) / 2)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨K, q / 2, by dsimp [K]; positivity, by positivity, by dsimp [q]; linarith, ?_⟩
  intro ρ d du hρ hd hρ₂ hdu hw hL2 hmoment hdiv
  let E := ∫ z, ∑ i, du i z ^ 2 ∂μ.prod (volume.restrict (unitOpenCube 3))
  have hE : 0 ≤ E := integral_nonneg fun z => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hEi : Integrable (fun z => ∑ i, du i z ^ 2) (μ.prod (volume.restrict (unitOpenCube 3))) :=
    integrable_finsetSum _ fun i _ => (hdu i).integrable_sq
  obtain ⟨v, hv, _, _, he⟩ := exists_H1_family_of_spatial_weak_partials hρ₂ hdu hw
  have he' : (∫⁻ t, ENNReal.ofReal (∑ i, ‖H1.derivative (unitOpenCube 3) i (v t)‖ ^ 2) ∂μ) =
      ENNReal.ofReal E := by
    have hh := he Set.univ
    simp only [Measure.restrict_univ] at hh
    rw [hh, ← ofReal_integral_eq_lintegral_ofReal hEi
      (Filter.Eventually.of_forall fun z => Finset.sum_nonneg fun i _ => sq_nonneg _)]
  have hm : ∀ᵐ t ∂μ, (∫⁻ x in unitOpenCube 3, ENNReal.ofReal |ρ (t, x)| ^ p₀) ≤
      ENNReal.ofReal (1 + R) := by
    filter_upwards [hmoment] with t ht
    apply (lintegral_rpow_le_measure_add (by linarith : 0 ≤ p₀) (min_le_left p 4)).trans
    simpa only [measure_univ, ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) hR,
      ENNReal.ofReal_one] using add_le_add (le_refl (1 : ℝ≥0∞)) ht
  exact integral_abs_compression_le_of_mixed_bounds hρ hd hb hq hq1.le hsum hexp
    (by linarith) hS hD hE hm
    (lintegral_cube_six_squared_le_of_H1_family v hR₂ hE hv hL2 he'.le) hdiv

end PDE
