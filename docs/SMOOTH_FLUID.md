# Smooth fluid identities

These modules provide the coordinate identities needed before a Navier–Stokes
existence or singular-limit argument. They use actual Mathlib derivatives and
integration by parts. The result statements do not assume the identities being proved.

## Conventions

- `Space n = Fin n → ℝ`; spatial derivatives use the existing `coordDeriv`.
- Fields depend on time first: `ρ : ℝ → Space n → ℝ` and
  `u : ℝ → Space n → Space n`.
- `fluidDot a b = ∑ i, a i * b i`. The ambient space has the supremum norm;
  kinetic energy is explicitly the physical sum of squares divided by two.
- `tensorDivergence A x i = ∑ j, ∂ⱼ Aᵢⱼ(x)`.
- Time derivatives are ordinary `deriv`; spatial derivatives are evaluations of
  `fderiv ℝ`. As in Mathlib, these operators are total functions. The classical
  chain rule and momentum theorems impose differentiability; algebraic residual
  identities only need the differentiability used by their product rules.

## 1. Material derivative

`hasDerivAt_material_along_characteristic` assumes joint differentiability of
`f(t,x)` at `(t,X(t))` and an actual derivative `X′(t) = u(t,X(t))`. It proves

```text
d/dt f(t,X(t)) = ∂ₜf(t,X(t)) + ∑ᵢ uᵢ(t,X(t)) ∂ᵢf(t,X(t)).
```

It derives the time and spatial slices from the joint Fréchet derivative and
applies the chain rule. The trajectory is supplied; flow existence and uniqueness
remain future work.

## 2. Continuity equation

`continuityResidual_eq_material` proves the pointwise identity

```text
∂ₜρ + div(ρu) = Dₜρ + ρ div u.
```

`satisfiesContinuityAt_iff_material` exposes equivalence of the zero-residual
equations with time and spatial differentiability hypotheses.
`divergence_eq_zero_of_material_density_constant` additionally requires `ρ ≠ 0`
to infer `div u = 0` from mass conservation and `Dₜρ = 0`.

## 3. Momentum forms

`conservativeMomentum_eq_material_add_continuity` proves, componentwise,

```text
∂ₜ(ρu) + div(ρu ⊗ u) = ρ(∂ₜu + (u·∇)u) + u(∂ₜρ + div(ρu)).
```

`conservativeMomentum_eq_of_continuity` eliminates the final term under the
continuity equation. `momentum_equation_iff_material` then identifies the two
equations with a supplied force **per unit volume**. These results do not divide
by density and therefore allow vacuum points. An acceleration equation divided
by density would need an additional nonzero-density hypothesis.

## 4. Newtonian viscous stress

For each C² velocity component and constant real `μ, λ`,
`tensorDivergence_newtonianStress` proves

```text
τᵢⱼ = μ(∂ⱼuᵢ + ∂ᵢuⱼ) + λ δᵢⱼ div u,
(div τ)ᵢ = μ Δuᵢ + (λ + μ) ∂ᵢ(div u).
```

The proof derives mixed coordinate derivative symmetry from Mathlib's C²
second-derivative symmetry theorem. It imposes no Stokes hypothesis or viscosity
positivity condition: this is an algebraic differential identity, not a
dissipation estimate. Variable viscosities require additional product-rule terms.
The divergence-free corollary assumes `div u = 0` as a spatial function, so its
gradient vanishes; zero divergence at a single point would not suffice.

## 5. Incompressible convection and kinetic energy

Let `u` have C¹ components on all of `Space n`, with `div u = 0` everywhere.
Let `v` have C¹ components and compact support. Then

```text
∫ ((u·∇)v) · v = 0.
```

`advection_kineticEnergy` proves the pointwise chain rule
`((u·∇)v)·v = u·∇(|v|²/2)`.
`integral_advection_eq_neg_divergence_mul` proves the spatial integration by
parts identity for every C¹ compactly supported scalar test. It verifies the
integrability of all products before applying integration by parts.
`integrable_kineticConvection` separately exposes the actual integrability of
the kinetic integrand. `incompressible_convection_energy_cancellation` takes
`v = u` to obtain the nonlinear convection cancellation.

The measure is whole-space Lebesgue measure. Compact support eliminates the
boundary contribution. Periodic domains, noncompact decay conditions, bounded
domains with traces, weak-solution testing, and the full time-dependent NS energy
identity are not covered by this checkpoint.

## Source and reuse notes

The requested topic selection follows the
[Navier–Stokes overview](https://en.wikipedia.org/wiki/Navier%E2%80%93Stokes_equations).
Mathematical references for the formulas are MIT's
[fluid mechanics chapter, equations 6.107–6.112](https://ocw.mit.edu/courses/8-09-classical-mechanics-iii-fall-2014/3bfed6897483f5c55bf615ed583af603_MIT8_09F14_Chapter_6.pdf)
and Ryzhik's
[Navier–Stokes notes, section 3.4](https://math.stanford.edu/~ryzhik/notes-256B-24.pdf).

Implementation reuses the pinned Mathlib modules `FDeriv.Mul`, `FDeriv.Prod`,
`FDeriv.CompCLM`, `FDeriv.Symmetric`, `Deriv.Comp`, `Deriv.Prod`, and
`LineDeriv.IntegrationByParts`. The reference submodule remains separate.
The concrete examples exercise simultaneous time/spatial dependence and a mixed
stress term with nonzero gradient of divergence.

See [STATUS](STATUS.md) for the archived full build and transitive axiom audit.
