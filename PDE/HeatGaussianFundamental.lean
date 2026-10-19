import PDE.HeatGaussianInitial
import PDE.HeatGaussianIntegrability
import PDE.HeatDistribution
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Fundamental-solution identity for the heat Gaussian

For a smooth compactly supported space–time test, differentiate its Gaussian
pairing at positive time and integrate by parts twice in each spatial coordinate.
The initial Dirac limit and the improper fundamental theorem of calculus give the
iterated test identity. Local integrability and Fubini then give the single
space–time integral identity in positive spatial dimension.

These results use product coordinates `(time, space)`. They establish the kernel
identity; the local representation of an arbitrary weak solution is still a
separate proof obligation.
-/

open MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators

namespace PDE

private theorem hasDerivAt_integral_on_compact {n : ℕ} {K : Set (Space n)}
    (hK : IsCompact K) {a ε : ℝ} (hε : 0 < ε)
    {F F' : ℝ × Space n → ℝ}
    (hF : ContinuousOn F (Icc (a - ε) (a + ε) ×ˢ K))
    (hF' : ContinuousOn F' (Icc (a - ε) (a + ε) ×ˢ K))
    (hd : ∀ x ∈ K, ∀ t ∈ Icc (a - ε) (a + ε),
      HasDerivAt (fun s => F (s, x)) (F' (t, x)) t) :
    HasDerivAt (fun t => ∫ x in K, F (t, x)) (∫ x in K, F' (a, x)) a := by
  have ha : a ∈ Icc (a - ε) (a + ε) := ⟨by linarith, by linarith⟩
  have hI : Icc (a - ε) (a + ε) ∈ 𝓝 a := Icc_mem_nhds (by linarith) (by linarith)
  have hi (t : ℝ) (ht : t ∈ Icc (a - ε) (a + ε)) :
      IntegrableOn (fun x => F (t, x)) K := by
    apply ContinuousOn.integrableOn_compact hK
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun x hx => ⟨ht, hx⟩)
  have hi' : IntegrableOn (fun x => F' (a, x)) K := by
    apply ContinuousOn.integrableOn_compact hK
    exact hF'.comp (continuous_const.prodMk continuous_id).continuousOn (fun x hx => ⟨ha, hx⟩)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hF'
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict K) (F := fun t x => F (t, x))
    (F' := fun t x => F' (t, x)) (bound := fun _ => C) hI
    (by filter_upwards [hI] with t ht; exact (hi t ht).aestronglyMeasurable)
    (hi a ha) hi'.aestronglyMeasurable
    (by filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
        exact fun t ht => hC (t, x) ⟨ht, hx⟩)
    (integrableOn_const hK.measure_lt_top.ne)
    (by filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
        exact hd x hx)).2

/-- Differentiate a compactly supported space–time test paired with the Gaussian
at positive time; this is before the spatial integrations by parts. -/
private theorem hasDerivAt_heatGaussian_pairing_raw {n : ℕ} {φ : ℝ × Space n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun t => ∫ x, heatGaussian t x * φ (t, x))
      (∫ x, ((∑ i, x i ^ 2) / (4 * a ^ 2) - n / (2 * a)) *
        heatGaussian a x * φ (a, x) +
        heatGaussian a x * fderiv ℝ φ (a, x) (1, 0)) a := by
  let K := Prod.snd '' tsupport φ
  have hK : IsCompact K := hc.image continuous_snd
  let F : ℝ × Space n → ℝ := fun p => heatGaussian p.1 p.2 * φ p
  let G : ℝ × Space n → ℝ := fun p =>
    ((∑ i, p.2 i ^ 2) / (4 * p.1 ^ 2) - n / (2 * p.1)) *
      heatGaussian p.1 p.2 * φ p + heatGaussian p.1 p.2 * fderiv ℝ φ p (1, 0)
  have hcφ : Continuous (fun p => fderiv ℝ φ p (1, 0)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hF : ContinuousOn F (Icc (a - a / 2) (a + a / 2) ×ˢ K) := by
    intro p hp
    have hp0 : 0 < p.1 := by have := hp.1.1; linarith
    exact ((heatGaussian_contDiffAt hp0).continuousAt.mul hφ.continuous.continuousAt).continuousWithinAt
  have hG : ContinuousOn G (Icc (a - a / 2) (a + a / 2) ×ˢ K) := by
    intro p hp
    have hp0 : 0 < p.1 := by have := hp.1.1; linarith
    have hH : ContinuousAt (fun q : ℝ × Space n => heatGaussian q.1 q.2) p :=
      (heatGaussian_contDiffAt hp0).continuousAt
    have hφc := hφ.continuous
    apply ContinuousAt.continuousWithinAt
    dsimp [G]
    fun_prop (disch := positivity)
  have hd : ∀ x ∈ K, ∀ t ∈ Icc (a - a / 2) (a + a / 2),
      HasDerivAt (fun s => F (s, x)) (G (t, x)) t := by
    intro x _ t ht
    have ht0 : 0 < t := by have := ht.1; linarith
    have hdφ : HasDerivAt (fun s => φ (s, x)) (fderiv ℝ φ (t, x) (1, 0)) t := by
      exact ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
    exact (hasDerivAt_heatGaussian_time ht0 x).mul hdφ
  have hz (t : ℝ) (x : Space n) (hx : x ∉ K) : (t, x) ∉ tsupport φ :=
    fun hp => hx ⟨(t, x), hp, rfl⟩
  have hFint (t : ℝ) : (∫ x in K, F (t, x)) = ∫ x, F (t, x) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [F, image_eq_zero_of_notMem_tsupport (hz t x hx)]
  have hGint (t : ℝ) : (∫ x in K, G (t, x)) = ∫ x, G (t, x) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [G, image_eq_zero_of_notMem_tsupport (hz t x hx),
      fderiv_of_notMem_tsupport ℝ (hz t x hx)]
  have h := hasDerivAt_integral_on_compact hK (half_pos ha) hF hG hd
  simpa only [hFint, hGint] using h

private theorem testFunction_slice {n : ℕ} {φ : ℝ × Space n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (t : ℝ) :
    IsTestFunctionOn univ (fun x => φ (t, x)) := by
  refine ⟨hφ.comp (contDiff_const.prodMk contDiff_id), ?_, subset_univ _⟩
  apply HasCompactSupport.of_support_subset_isCompact (hc.image continuous_snd)
  intro x hx
  exact ⟨(t, x), subset_tsupport φ hx, rfl⟩

private theorem gaussian_laplacian_pairing {n : ℕ} (t : ℝ) {ψ : Space n → ℝ}
    (hψ : IsTestFunctionOn univ ψ) :
    (∫ x, laplacian (heatGaussian t) x * ψ x) =
      ∫ x, heatGaussian t x * laplacian ψ x := by
  have hi (i : Fin n) : Integrable (fun x =>
      coordDeriv i (coordDeriv i (heatGaussian t)) x * ψ x) := by
    have hc := contDiffOn_coordDeriv_infty isOpen_univ
      (contDiffOn_coordDeriv_infty isOpen_univ (heatGaussian_contDiff_space t).contDiffOn i) i
    apply integrable_mul_of_locallyIntegrableOn
      (hc.continuousOn.locallyIntegrableOn MeasurableSet.univ)
      hψ.contDiff.continuous hψ.hasCompactSupport hψ.tsupport_subset
  have hj (i : Fin n) : Integrable (fun x =>
      heatGaussian t x * coordDeriv i (coordDeriv i ψ) x) := by
    have hd := (hψ.coordDeriv i).coordDeriv i
    apply integrable_mul_of_locallyIntegrableOn
      ((heatGaussian_contDiff_space t).continuous.continuousOn.locallyIntegrableOn
        MeasurableSet.univ) hd.contDiff.continuous hd.hasCompactSupport hd.tsupport_subset
  simp only [laplacian, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hi i), integral_finsetSum _ (fun i _ => hj i)]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [setIntegral_univ] using
    (integral_coordDeriv_twice_mul isOpen_univ (heatGaussian_contDiff_space t).contDiffOn hψ i).symm

/-- The heat adjoint on product coordinates, with the time coordinate first. -/
noncomputable def heatProductAdjoint {n : ℕ} (φ : ℝ × Space n → ℝ)
    (p : ℝ × Space n) : ℝ :=
  fderiv ℝ φ p (1, 0) + ∑ i : Fin n,
    fderiv ℝ (fun q => fderiv ℝ φ q (0, Pi.single i 1)) p (0, Pi.single i 1)

private theorem contDiff_directional {n : ℕ} {φ : ℝ × Space n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (v : ℝ × Space n) :
    ContDiff ℝ ∞ (fun p => fderiv ℝ φ p v) :=
  (hφ.fderiv_right (by simp)).clm_apply contDiff_const

private theorem coordDeriv_slice {n : ℕ} {φ : ℝ × Space n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (t : ℝ) (x : Space n) (i : Fin n) :
    coordDeriv i (fun y => φ (t, y)) x = fderiv ℝ φ (t, x) (0, Pi.single i 1) := by
  have hd := ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x))
  simp only [Function.comp_def, id_eq] at hd
  unfold coordDeriv
  rw [hd.fderiv]
  rfl

private theorem heatProductAdjoint_eq {n : ℕ} {φ : ℝ × Space n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (p : ℝ × Space n) :
    heatProductAdjoint φ p = fderiv ℝ φ p (1, 0) +
      laplacian (fun x => φ (p.1, x)) p.2 := by
  simp only [heatProductAdjoint, laplacian]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he : coordDeriv i (fun x => φ (p.1, x)) =
      (fun x => fderiv ℝ φ (p.1, x) (0, Pi.single i 1)) := by
    ext x
    exact coordDeriv_slice hφ p.1 x i
  rw [he, coordDeriv_slice (contDiff_directional hφ (0, Pi.single i 1))]

/-- Differentiate the Gaussian pairing and transfer spatial derivatives to the
compactly supported test function. -/
theorem hasDerivAt_heatGaussian_pairing {n : ℕ} {φ : ℝ × Space n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, heatGaussian s x * φ (s, x))
      (∫ x, heatGaussian t x * heatProductAdjoint φ (t, x)) t := by
  have hψ := testFunction_slice hφ hc t
  have htime := testFunction_slice (contDiff_directional hφ (1, 0))
    (hc.fderiv_apply ℝ (1, 0)) t
  have hH := (heatGaussian_contDiff_space (n := n) t).continuous
  have hitime : Integrable (fun x => heatGaussian t x * fderiv ℝ φ (t, x) (1, 0)) :=
    (hH.mul htime.contDiff.continuous).integrable_of_hasCompactSupport htime.hasCompactSupport.mul_left
  have hilap : Integrable (fun x => laplacian (heatGaussian t) x * φ (t, x)) := by
    have hcl : Continuous (laplacian (heatGaussian (n := n) t)) := by
      change Continuous (fun x : Space n => ∑ i, coordDeriv i (coordDeriv i (heatGaussian t)) x)
      exact continuous_finsetSum _ (fun i _ => by
        exact continuousOn_univ.mp (contDiffOn_coordDeriv_infty isOpen_univ
          (contDiffOn_coordDeriv_infty isOpen_univ (heatGaussian_contDiff_space t).contDiffOn i) i).continuousOn)
    exact (hcl.mul hψ.contDiff.continuous).integrable_of_hasCompactSupport hψ.hasCompactSupport.mul_left
  have hjlap : Integrable (fun x => heatGaussian t x * laplacian (fun y => φ (t, y)) x) := by
    simp only [laplacian, Finset.mul_sum]
    apply integrable_finsetSum
    intro i _
    have hd := (hψ.coordDeriv i).coordDeriv i
    exact (hH.mul hd.contDiff.continuous).integrable_of_hasCompactSupport hd.hasCompactSupport.mul_left
  have he (x : Space n) :
      ((∑ i, x i ^ 2) / (4 * t ^ 2) - n / (2 * t)) * heatGaussian t x =
        laplacian (heatGaussian t) x := by
    rw [← heatGaussian_solves_heat ht x, (hasDerivAt_heatGaussian_time ht x).deriv]
  apply (hasDerivAt_heatGaussian_pairing_raw hφ hc ht).congr_deriv
  simp only [he, heatProductAdjoint_eq hφ, mul_add]
  rw [integral_add hilap hitime, integral_add hitime hjlap,
    gaussian_laplacian_pairing t hψ, add_comm]

private theorem heatProductAdjoint_contDiff {n : ℕ} {φ : ℝ × Space n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (heatProductAdjoint φ) :=
  (contDiff_directional hφ (1, 0)).add (ContDiff.sum (fun i _ =>
    contDiff_directional (contDiff_directional hφ (0, Pi.single i 1)) (0, Pi.single i 1)))

private theorem heatProductAdjoint_eq_zero {n : ℕ} {φ : ℝ × Space n → ℝ}
    {p : ℝ × Space n} (hp : p ∉ tsupport φ) : heatProductAdjoint φ p = 0 := by
  have hz (i : Fin n) :
      fderiv ℝ (fun q => fderiv ℝ φ q (0, Pi.single i 1)) p (0, Pi.single i 1) = 0 := by
    rw [fderiv_of_notMem_tsupport ℝ
      (fun h => hp ((tsupport_fderiv_apply_subset ℝ (0, Pi.single i 1)) h))]
    rfl
  simp [heatProductAdjoint, fderiv_of_notMem_tsupport ℝ hp, hz]

private theorem heatProductAdjoint_hasCompactSupport {n : ℕ} {φ : ℝ × Space n → ℝ}
    (hc : HasCompactSupport φ) : HasCompactSupport (heatProductAdjoint φ) := by
  apply HasCompactSupport.of_support_subset_isCompact hc.isCompact
  intro p hp
  by_contra hn
  exact hp (heatProductAdjoint_eq_zero hn)

private noncomputable def gaussianTestPairing {n : ℕ} (φ : ℝ × Space n → ℝ) (t : ℝ) : ℝ :=
  if t = 0 then φ (0, 0) else ∫ x, heatGaussian t x * φ (t, x)

private theorem gaussianTestPairing_hasDerivAt {n : ℕ} {φ : ℝ × Space n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (gaussianTestPairing φ)
      (∫ x, heatGaussian t x * heatProductAdjoint φ (t, x)) t := by
  apply (hasDerivAt_heatGaussian_pairing hφ hc ht).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds ht.ne'] with s hs
  simp [gaussianTestPairing, hs]

private theorem gaussianTestPairing_continuousOn {n : ℕ} {φ : ℝ × Space n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ContinuousOn (gaussianTestPairing φ) (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  rcases ht.eq_or_lt with hzero | hpos
  · subst t
    apply continuousWithinAt_Ioi_iff_Ici.mp
    obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hφ.continuous
    have h := heatGaussian_tendsto_initial_joint hφ.continuous hC
    change Tendsto _ _ (𝓝 (gaussianTestPairing φ 0))
    simp only [gaussianTestPairing, ite_true]
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp [gaussianTestPairing, ne_of_gt (show (0 : ℝ) < s from hs)]
  · exact (gaussianTestPairing_hasDerivAt hφ hc hpos).continuousAt.continuousWithinAt

private theorem gaussianTestPairing_zero_after {n : ℕ} {φ : ℝ × Space n → ℝ}
    (hc : HasCompactSupport φ) : ∃ R > 0, ∀ t > R, gaussianTestPairing φ t = 0 := by
  obtain ⟨R, hR, hb⟩ := hc.isCompact.isBounded.exists_pos_norm_le
  refine ⟨R, hR, fun t ht => ?_⟩
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans hR ht)
  simp only [gaussianTestPairing, ite_eq_right ht0]
  apply integral_eq_zero_of_ae
  apply ae_of_all
  intro x
  have hp : (t, x) ∉ tsupport φ := by
    intro hp
    have hb' := hb (t, x) hp
    have htn : t ≤ ‖(t, x)‖ := (le_abs_self t).trans (norm_fst_le (t, x))
    linarith
  change heatGaussian t x * φ (t, x) = 0
  rw [image_eq_zero_of_notMem_tsupport hp, mul_zero]

private theorem gaussianTestPairing_integrableOn {n : ℕ} {φ : ℝ × Space n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    IntegrableOn (gaussianTestPairing φ) (Ioi 0) := by
  obtain ⟨R, hR, hz⟩ := gaussianTestPairing_zero_after hc
  have hfirst : IntegrableOn (gaussianTestPairing φ) (Ioc 0 R) :=
    ((gaussianTestPairing_continuousOn hφ hc).mono Icc_subset_Ici_self).integrableOn_compact
      isCompact_Icc |>.mono_set Ioc_subset_Icc_self
  have hlast : IntegrableOn (gaussianTestPairing φ) (Ioi R) := by
    apply (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioi R) volume).congr_fun
    · intro t ht
      exact (hz t ht).symm
    · exact isOpen_Ioi.measurableSet
  apply (hfirst.union hlast).mono_set
  intro t ht
  by_cases htr : t ≤ R
  · exact Or.inl ⟨ht, htr⟩
  · exact Or.inr (lt_of_not_ge htr)

/-- The normalized Gaussian is a fundamental solution: its pairing with the
heat adjoint of a compact smooth space–time test is minus evaluation at the source. -/
theorem integral_heatGaussian_adjoint {n : ℕ} {φ : ℝ × Space n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ t in Ioi 0, ∫ x, heatGaussian t x * heatProductAdjoint φ (t, x)) = -φ (0, 0) := by
  have hi := gaussianTestPairing_integrableOn (heatProductAdjoint_contDiff hφ)
    (heatProductAdjoint_hasCompactSupport hc)
  have hi' : IntegrableOn (fun t => ∫ x, heatGaussian t x * heatProductAdjoint φ (t, x))
      (Ioi 0) := by
    apply hi.congr_fun
    · intro t ht
      simp [gaussianTestPairing, ne_of_gt (show (0 : ℝ) < t from ht)]
    · exact isOpen_Ioi.measurableSet
  have hlim : Tendsto (gaussianTestPairing φ) atTop (𝓝 0) := by
    obtain ⟨R, _, hR⟩ := gaussianTestPairing_zero_after hc
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop R] with t ht
    exact (hR t ht).symm
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (gaussianTestPairing_continuousOn hφ hc 0 (by simp))
    (fun t ht => gaussianTestPairing_hasDerivAt hφ hc ht) hi' hlim
  simpa only [gaussianTestPairing, ite_true, zero_sub] using h

/-- The fundamental-solution identity as a single Lebesgue integral on space–time.
The adjoint pairing is absolutely integrable, including across time zero. -/
theorem integral_heatGaussian_adjoint_volume {n : ℕ} (hn : 0 < n)
    {φ : ℝ × Space n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ p : ℝ × Space n, heatGaussian p.1 p.2 * heatProductAdjoint φ p) = -φ (0, 0) := by
  have hi := heatGaussian_integrable_test hn (heatProductAdjoint_contDiff hφ).continuous
    (heatProductAdjoint_hasCompactSupport hc)
  calc
    (∫ p : ℝ × Space n, heatGaussian p.1 p.2 * heatProductAdjoint φ p) =
        ∫ t, ∫ x, heatGaussian t x * heatProductAdjoint φ (t, x) := integral_prod _ hi
    _ = ∫ t in Ioi 0, ∫ x, heatGaussian t x * heatProductAdjoint φ (t, x) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      simp only [heatGaussian_eq_zero_of_nonpos hn (le_of_not_gt ht), zero_mul, integral_zero]
    _ = -φ (0, 0) := integral_heatGaussian_adjoint hφ hc

end PDE
