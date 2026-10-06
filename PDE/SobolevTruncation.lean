import PDE.SobolevH1
import PDE.ClassicalWeakDerivative
import PDE.CubeWeakPositivePart

/-! Constants and lower-level positive truncations in the actual H¹ graph space.
The cube truncation has its distributional gradient, with zero slope on the
threshold, without a zero-trace condition. -/

open MeasureTheory Set
open scoped ENNReal

namespace PDE

theorem HasWeakPartialOn.const {n : ℕ} (Ω : Set (Space n)) (i : Fin n) (c : ℝ) :
    HasWeakPartialOn Ω i (fun _ => c) (fun _ => 0) := by
  have h := hasWeakPartialOn_of_contDiffOn isOpen_univ i
    (contDiff_const.contDiffOn : ContDiffOn ℝ 1 (fun _ : Space n => c) univ)
  have h' : HasWeakPartialOn univ i (fun _ : Space n => c) (fun _ => 0) := by
    apply h.congr Filter.EventuallyEq.rfl
    exact Filter.Eventually.of_forall fun x => by simp [coordDeriv]
  exact h'.mono (subset_univ Ω)

theorem HasWeakPartialOn.const_sub {n : ℕ} {Ω : Set (Space n)} {i : Fin n}
    {u du : Space n → ℝ} (hu : HasWeakPartialOn Ω i u du) (c : ℝ) :
    HasWeakPartialOn Ω i (fun x => c - u x) (fun x => -du x) := by
  have h := (HasWeakPartialOn.const Ω i c).add (hu.smul (-1))
  change HasWeakPartialOn Ω i (fun x => c + (-1) * u x) (fun x => 0 + (-1) * du x) at h
  simpa only [neg_one_mul, zero_add, sub_eq_add_neg] using h

namespace H1

noncomputable def const {n : ℕ} (Ω : Set (Space n))
    [IsFiniteMeasure (volume.restrict Ω)] (c : ℝ) : H1 Ω :=
  ofFunction (fun _ => c) (fun _ _ => 0) (memLp_const c)
    (fun _ => MemLp.zero) (fun i => HasWeakPartialOn.const Ω i c)

theorem value_const_ae {n : ℕ} (Ω : Set (Space n))
    [IsFiniteMeasure (volume.restrict Ω)] (c : ℝ) :
    value Ω (const Ω c) =ᵐ[volume.restrict Ω] (fun _ => c) :=
  value_ofFunction_ae _ _ _ _ _

theorem derivative_const_ae {n : ℕ} (Ω : Set (Space n))
    [IsFiniteMeasure (volume.restrict Ω)] (c : ℝ) (i : Fin n) :
    derivative Ω i (const Ω c) =ᵐ[volume.restrict Ω] (fun _ => 0) :=
  derivative_ofFunction_ae _ _ _ _ _ i

private theorem lowerTruncation_weak {n : ℕ}
    (u : H1 (unitOpenCube (n + 1))) (c : ℝ) (i : Fin (n + 1)) :
    HasWeakPartialOn (unitOpenCube (n + 1)) i
      (fun x => max (c - value (unitOpenCube (n + 1)) u x) 0)
      (fun x => if value (unitOpenCube (n + 1)) u x < c then
        -derivative (unitOpenCube (n + 1)) i u x else 0) := by
  have h := ((u.hasWeakPartialOn i).const_sub c).unitOpenCube_positivePart
    ((memLp_const c).sub (Lp.memLp (value (unitOpenCube (n + 1)) u)))
    (Lp.memLp (derivative (unitOpenCube (n + 1)) i u)).neg
  simpa only [sub_pos] using h

noncomputable def lowerTruncation {n : ℕ} (u : H1 (unitOpenCube (n + 1)))
    (c : ℝ) : H1 (unitOpenCube (n + 1)) :=
  ofFunction (fun x => max (c - value (unitOpenCube (n + 1)) u x) 0)
    (fun i x => if value (unitOpenCube (n + 1)) u x < c then
      -derivative (unitOpenCube (n + 1)) i u x else 0)
    (((memLp_const c).sub (Lp.memLp (value (unitOpenCube (n + 1)) u))).pos_part)
    (fun i => by
      simpa only [sub_pos] using memLp_positivePart_derivative
        (u := fun x => c - value (unitOpenCube (n + 1)) u x)
        (du := fun x => -derivative (unitOpenCube (n + 1)) i u x)
        (aemeasurable_const.sub (Lp.aestronglyMeasurable
          (value (unitOpenCube (n + 1)) u)).aemeasurable)
        (Lp.memLp (derivative (unitOpenCube (n + 1)) i u)).neg)
    (lowerTruncation_weak u c)

theorem value_lowerTruncation_ae {n : ℕ} (u : H1 (unitOpenCube (n + 1))) (c : ℝ) :
    value (unitOpenCube (n + 1)) (u.lowerTruncation c) =ᵐ[volume.restrict (unitOpenCube (n + 1))]
      (fun x => max (c - value (unitOpenCube (n + 1)) u x) 0) :=
  value_ofFunction_ae _ _ _ _ _

theorem derivative_lowerTruncation_ae {n : ℕ} (u : H1 (unitOpenCube (n + 1)))
    (c : ℝ) (i : Fin (n + 1)) :
    derivative (unitOpenCube (n + 1)) i (u.lowerTruncation c) =ᵐ[volume.restrict (unitOpenCube (n + 1))]
      (fun x => if value (unitOpenCube (n + 1)) u x < c then
        -derivative (unitOpenCube (n + 1)) i u x else 0) :=
  derivative_ofFunction_ae _ _ _ _ _ i

theorem ofReal_gradientEnergy_eq_lintegral {n : ℕ} {Ω : Set (Space n)} (u : H1 Ω) :
    ENNReal.ofReal (∑ i : Fin n, ‖derivative Ω i u‖ ^ 2) =
      ∫⁻ x in Ω, ENNReal.ofReal (∑ i : Fin n, derivative Ω i u x ^ 2) := by
  rw [← u.integral_gradient_sq]
  exact ofReal_integral_eq_lintegral_ofReal
    (integrable_finsetSum _ (fun i _ => (Lp.memLp (derivative Ω i u)).integrable_sq))
    (Filter.Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

end H1
end PDE
