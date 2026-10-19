# Interior smoothness of weak heat solutions

The interior regularity theorem is proved in Lean as `PDE.heat_interior_smooth`.
It gives joint space–time smoothness for locally integrable distributional
solutions of the homogeneous heat equation with diffusivity one. The stronger
`PDE.IsDistributionalHeatSolution.exists_smooth_representative` applies on any
open space–time set, not only a product cylinder.

## English statement

Let \(n\geq 1\), let \(\Omega\subseteq\mathbb R^n\) be open, let \(T>0\), and set
\(Q=(0,T)\times\Omega\). Suppose \(u\in L^1_{\mathrm{loc}}(Q)\) solves
\(\partial_tu-\Delta_xu=0\) in the sense of distributions: for every
\(\varphi\in C_c^\infty(Q)\),

\[
\int_Q u(t,x)\bigl(\partial_t\varphi(t,x)+\Delta_x\varphi(t,x)\bigr)
\,dt\,dx=0.
\]

**There exists \(v\in C^\infty(Q)\) such that \(u=v\) almost everywhere on
\(Q\), and \(\partial_tv=\Delta_xv\) at every point of \(Q\). This smooth
representative is unique on \(Q\).**

Here \(C^\infty\) means joint smoothness: all mixed time and space derivatives
of every finite order exist and are continuous. Because a weak solution is an
almost-everywhere object, the theorem produces a smooth representative; it does
not assert smoothness of every pointwise version of \(u\). Extensions outside
\(Q\) are not unique.

No boundedness, connectedness, Lipschitz boundary, boundary condition, or initial
datum is assumed. There is no conclusion at \(t=0\), \(t=T\), or
\(x\in\partial\Omega\), and no uniform derivative bound approaching the boundary.

## Why an irregular boundary is allowed

Every interior point has a smaller space–time neighborhood with compact closure
inside \(Q\). The proof localizes there; rough boundary geometry does not affect
this interior conclusion. Such geometry can affect regularity up to the boundary.
An unbounded slope in one graph representation, such as \(y=\sqrt{x}\), does not
by itself establish that a domain is non-Lipschitz, since boundary charts allow
rotation and the surrounding domain matters.

For a classical reference, Nicolas Lerner's
[lecture notes](https://webusers.imj-prg.fr/~nicolas.lerner/pde-m1-lerner.pdf),
Definition 3.1.3 and Corollary 3.2.2, state heat-operator hypoellipticity on arbitrary
open sets. The Lean result below has its own checked proof.

## Lean statement and proof application

The repository uses `Space (n + 1) = Fin (n + 1) → ℝ`. Coordinate `0` is time;
coordinates `i.succ` are spatial coordinates. Lebesgue measure is on all \(n+1\)
coordinates. The following example states the English theorem exactly and proves
it by applying the implemented theorem; it is not merely a proposition checked
with `#check`.

```lean
import PDE.HeatInteriorRegularity

open MeasureTheory Set
open scoped ContDiff BigOperators

namespace PDE.HeatInteriorSpecification

example (n : ℕ) (hn : 0 < n)
    (Ω : Set (Space n)) (hΩ : IsOpen Ω)
    (T : ℝ) (hT : 0 < T)
    (u : Space (n + 1) → ℝ)
    (hu : IsDistributionalHeatSolution (heatCylinder Ω T) u) :
    ∃ v : Space (n + 1) → ℝ,
      ContDiffOn ℝ ∞ v (heatCylinder Ω T) ∧
      u =ᵐ[volume.restrict (heatCylinder Ω T)] v ∧
      (∀ z ∈ heatCylinder Ω T,
        coordDeriv 0 v z = spaceTimeLaplacian v z) ∧
      (∀ w : Space (n + 1) → ℝ,
        ContDiffOn ℝ ∞ w (heatCylinder Ω T) →
        u =ᵐ[volume.restrict (heatCylinder Ω T)] w →
        EqOn w v (heatCylinder Ω T)) :=
  heat_interior_smooth hn hΩ hT hu

end PDE.HeatInteriorSpecification
```

The plus sign in the test equation is intentional. Moving the time derivative
onto a test gives a minus sign, while moving two spatial derivatives gives a plus
sign; multiplying the resulting zero identity by minus one gives the displayed
formula. Local integrability and compact test support justify the pairings.

## Checked proof

1. Localize the weak solution to a compact subset of the open domain and convolve
   it with normalized smooth bumps. The resulting functions are smooth, converge
   almost everywhere and in local L¹, and eventually solve the heat equation
   uniformly across each compact interior subset.
2. Construct the normalized causal Gaussian in arbitrary positive spatial
   dimension. Prove its heat equation, unit spatial mass, initial Dirac limit,
   smoothness away from the source, and local integrability across the source.
   Differentiation under the integral, spatial integration by parts, improper
   FTC, and Fubini give the fundamental-solution identity
   \(\int H(\partial_t\varphi+\Delta_x\varphi)=-\varphi(0,0)\).
3. Transport that identity to the repository's coordinate-zero time convention,
   preserving Lebesgue measure. For a smooth caloric function and a compact smooth
   cutoff χ equal to one near z, prove
   \[
   u(z)=\int H(z-y)u(y)(\partial_t\chi+\Delta_x\chi)(y)\,dy
    -2\sum_i\int (\partial_{x_i}H)(z-y)u(y)\partial_{x_i}\chi(y)\,dy.
   \]
   All solution derivatives have been transferred to the cutoff and kernel.
4. The differentiated cutoff supports avoid z. On a common neighborhood, replace
   each kernel by a compactly supported smooth kernel agreeing on every relevant
   support difference. Pass the formula through strong L¹ convergence of the
   mollifications. Smooth convolution gives a local smooth function, and the
   almost-everywhere limit identifies it with the original solution.
5. Continuous representatives agreeing almost everywhere agree pointwise on open
   overlaps. Glue the local representatives; a countable subcover preserves a.e.
   equality on the whole domain. Finally, the already proved equivalence between
   distributional and classical equations for smooth functions supplies the
   pointwise heat equation. The same continuous uniqueness lemma proves uniqueness.

Smoothness of the approximating sequence alone is never used as a substitute for
smoothness of its limit. The fixed smooth convolution representation proves the
latter directly.

## Implementation map

| Module | Role |
|---|---|
| `HeatDistribution` | Weak equation, test calculus, integrability, a.e. invariance, continuous uniqueness, smooth classical equivalence |
| `HeatMollification`, `HeatApproximation`, `HeatApproximationL1` | Localization, smooth caloric approximations, a.e. and strong L¹ convergence |
| `HeatGaussian`, `HeatGaussianInitial`, `HeatGaussianCausal` | Normalization, explicit derivatives, initial limit, smoothness off the source |
| `HeatGaussianIntegrability`, `HeatGaussianFundamental` | Space–time integrability and fundamental-solution identity |
| `HeatGaussianCoordinates`, `HeatCutoffRepresentation` | Coordinate conversion and cutoff representation without solution derivatives |
| `HeatKernelExtension` | Fixed compact smooth replacements for all relevant kernels |
| `HeatLocalRegularity` | Smooth local representatives of arbitrary distributional heat solutions |
| `HeatInteriorRegularity` | Gluing, the open-domain theorem, and the stated cylinder corollary |

## Separate energy-space interoperability

The proved theorem takes `IsDistributionalHeatSolution`, exactly as stated above.
The older `PDE.IsIntegratedWeakHeatSolution` instead concerns a Bochner a.e. class
in `HeatEnergySpace Ω hΩ T`. A formal adapter from that API remains future work:
construct a jointly measurable scalar representative, establish local
integrability, and derive the distributional identity for arbitrary smooth
space–time tests from its time/spatial test formulation. No such adapter is
claimed by the present theorem. The documented English and Lean statements
both use the distributional solution class and do not require this adapter.

## Verification

On 2026-10-18, `bash scripts/check.sh` passed for the full library and all five
example modules, with 560 named theorem roots audited. The 82 new heat roots,
including `PDE.heat_interior_smooth`, depend only on `propext`, `Classical.choice`,
and `Quot.sound`. No `sorry` or new axioms are used. `reports/latest.json` records
the checked source hashes and audit; independent kernel replay is not included.

`Checks/HeatInteriorExamples.lean` checks the signs using the nonconstant caloric
polynomial u(t,x) = x² + 2t and applies the regularity theorem to an arbitrary
weak solution on an open cusp. No boundary regularity predicate is introduced.

Run `python3 scripts/check-heat-interior-statement.py` to compile the exact Lean
example in this document, including its application of the proved theorem.
The toolchain remains Lean `4.34.0-rc2` with pinned Mathlib revision
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. Compilation is serial under the existing
memory limiter, with a 3000 MiB Lean budget and a 3500 MiB build-tree RSS guard.
