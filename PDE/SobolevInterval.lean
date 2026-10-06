import PDE.DistributionalInterval
import PDE.SobolevH1
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# The actual distributional H¹ space on an interval

The one-coordinate space `Fin 1 → ℝ` is identified with `ℝ` by a
measure-preserving continuous linear equivalence. Compact tests and their
actual derivatives are transported. This connects the existing H¹ graph to
the compact-test reconstruction and mean Poincaré, without an ACL assumption.
Higher-dimensional first-coordinate slicing is proved in `PDE.SobolevSlicing`.
-/

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace PDE

/-- The open interval in the existing one-coordinate spatial representation. -/
def intervalDomain (a b : ℝ) : Set (Space 1) := {x | x 0 ∈ Ioo a b}

theorem isOpen_intervalDomain (a b : ℝ) : IsOpen (intervalDomain a b) :=
  isOpen_Ioo.preimage (continuous_apply 0)

/-- Endpoints are null: the closed real interval and open spatial interval
have the same measure under the constant-coordinate parametrization. -/
theorem intervalLift_measurePreserving (a b : ℝ) :
    MeasurePreserving (fun t : ℝ => fun _ : Fin 1 => t)
      (volume.restrict (Icc a b)) (volume.restrict (intervalDomain a b)) := by
  have h := (volume_preserving_funUnique (Fin 1) ℝ).restrict_preimage
    (s := Ioo a b) measurableSet_Ioo
  change MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ)
    (volume.restrict (intervalDomain a b)) (volume.restrict (Ioo a b)) at h
  have hsymm := MeasurePreserving.symm (MeasurableEquiv.funUnique (Fin 1) ℝ) h
  rwa [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hsymm

theorem integral_intervalLift (a b : ℝ) (f : Space 1 → ℝ) :
    (∫ t in Icc a b, f (fun _ => t)) = ∫ x in intervalDomain a b, f x :=
  (intervalLift_measurePreserving a b).integral_comp
    (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurableEmbedding f

/-- A scalar test derivative is exactly the single spatial coordinate derivative. -/
theorem coordDeriv_interval_test {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) (x : Space 1) :
    coordDeriv 0 (fun y : Space 1 => φ (y 0)) x = deriv φ (x 0) := by
  have hd := (hφ (x 0)).hasDerivAt.comp_hasFDerivAt x
    (ContinuousLinearMap.proj (0 : Fin 1) : Space 1 →L[ℝ] ℝ).hasFDerivAt
  have hd' : HasFDerivAt (fun y : Space 1 => φ (y 0))
      (deriv φ (x 0) • (ContinuousLinearMap.proj (0 : Fin 1) : Space 1 →L[ℝ] ℝ)) x := hd
  unfold coordDeriv
  rw [hd'.fderiv]
  simp

/-- Transport the actual compact-test distributional relation from `Space 1`.
The L² premises supply whole-interval integrability, not regularity of a representative. -/
theorem HasWeakPartialOn.to_interval
    {a b : ℝ} {u du : Space 1 → ℝ}
    (hu : HasWeakPartialOn (intervalDomain a b) 0 u du)
    (hu2 : MemLp u 2 (volume.restrict (intervalDomain a b)))
    (hd2 : MemLp du 2 (volume.restrict (intervalDomain a b))) :
    HasWeakDerivativeOnInterval a b (fun t => u (fun _ => t)) (fun t => du (fun _ => t)) := by
  have hui := (hu2.comp_measurePreserving (intervalLift_measurePreserving a b)).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hdi := (hd2.comp_measurePreserving (intervalLift_measurePreserving a b)).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨hui, hdi, ?_⟩
  intro φ hφ hc hs
  let e := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
  have ht : IsTestFunctionOn (intervalDomain a b) (fun x => φ (x 0)) := by
    refine ⟨hφ.comp (by fun_prop : ContDiff ℝ ∞ (fun x : Space 1 => x 0)),
      hc.comp_homeomorph e.toHomeomorph, ?_⟩
    have heq := tsupport_comp_eq_preimage φ e.toHomeomorph
    intro x hx
    change x 0 ∈ Ioo a b
    apply hs
    exact (Set.ext_iff.mp heq x).mp hx
  have hid := hu.integration_by_parts _ ht
  have hcder (x : Space 1) := coordDeriv_interval_test (hφ.differentiable (by simp)) x
  simp only [hcder] at hid
  have hl := integral_intervalLift a b (fun x => u x * deriv φ (x 0))
  have hr := integral_intervalLift a b (fun x => du x * φ (x 0))
  simpa only [smul_eq_mul, mul_comm] using (hl.trans (hid.trans (congrArg Neg.neg hr.symm)))

/-- An element of the existing H¹ graph has an actual AC representative in
the interval coordinate, with its genuine H¹ weak derivative. -/
theorem H1.exists_interval_absolutelyContinuous_representative
    {a b : ℝ} (hab : a < b) (u : H1 (intervalDomain a b)) :
    ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v a b ∧
      (fun t => H1.value (intervalDomain a b) u (fun _ => t)) =ᵐ[volume.restrict (Icc a b)] v ∧
      deriv v =ᵐ[volume.restrict (Icc a b)]
        (fun t => H1.derivative (intervalDomain a b) 0 u (fun _ => t)) :=
  ((u.hasWeakPartialOn 0).to_interval (Lp.memLp _) (Lp.memLp _)).exists_absolutelyContinuous_representative hab

/-- Mean Poincaré on the actual H¹ graph, with no zero-boundary requirement
and no geometric estimate as an input. -/
theorem H1.interval_mean_poincare {a b : ℝ} (hab : a < b) (u : H1 (intervalDomain a b)) :
    (∫ x in intervalDomain a b,
      (H1.value (intervalDomain a b) u x -
        (∫ y in intervalDomain a b, H1.value (intervalDomain a b) u y) / (b - a)) ^ 2) ≤
      (b - a) ^ 2 * ∫ x in intervalDomain a b, H1.derivative (intervalDomain a b) 0 u x ^ 2 := by
  have hw := (u.hasWeakPartialOn 0).to_interval (Lp.memLp _) (Lp.memLp _)
  have hv := (Lp.memLp (H1.value (intervalDomain a b) u)).comp_measurePreserving
    (intervalLift_measurePreserving a b)
  have hd := (Lp.memLp (H1.derivative (intervalDomain a b) 0 u)).comp_measurePreserving
    (intervalLift_measurePreserving a b)
  have h := hw.mean_poincare hab hv hd
  have hm := integral_intervalLift a b (fun x => H1.value (intervalDomain a b) u x)
  rw [hm] at h
  have hl := integral_intervalLift a b (fun x =>
    (H1.value (intervalDomain a b) u x -
      (∫ y in intervalDomain a b, H1.value (intervalDomain a b) u y) / (b - a)) ^ 2)
  have hr := integral_intervalLift a b (fun x => H1.derivative (intervalDomain a b) 0 u x ^ 2)
  rwa [hl, hr] at h

end PDE
