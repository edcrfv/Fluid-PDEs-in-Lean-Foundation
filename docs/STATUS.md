# Foundation implementation status

This standalone snapshot retains the shared PDE foundation and 478 public theorem
audit roots. Its verification scope is `PDE` and foundation-only `Checks`.
See `reports/latest.json` after running `bash scripts/check.sh` for the current
build, source hashes and axiom audit. No research-project result is included.

The standalone snapshot passed `bash scripts/check.sh` on 2026-10-06: both
default targets built successfully and all 478 named roots passed the allowed
axiom audit. The [snapshot report](../reports/foundation-verification.json)
records the actual source hashes and links to the retained build/audit logs.
This is not an independent kernel replay.

## Smooth fluid identities

The five additions and their exact hypotheses are documented in
[SMOOTH_FLUID](SMOOTH_FLUID.md). Their 34 new public roots include coordinate adapters
and integrability lemmas; they are not 34 independent fluid PDE results.

- `hasDerivAt_material_along_characteristic`: actual chain rule for a jointly
  differentiable time-dependent field along a supplied differentiable trajectory.
- `satisfiesContinuityAt_iff_material`: equivalence of conservative and material
  mass equations under the stated first-derivative assumptions.
- `conservativeMomentum_eq_material_add_continuity`: full momentum identity with the
  mass residual; under continuity, the two momentum equations agree without division by density.
- `tensorDivergence_newtonianStress`: C² components and constant viscosities give
  `div τ = μ Δu + (λ + μ) grad(div u)`, using proved mixed-partial symmetry.
- `incompressible_convection_energy_cancellation`: for C¹ compact-support divergence-free
  velocity on all of `Space n`, `∫ ((u·∇)u)·u = 0`. The more general result permits a
  distinct transported compact-support field, and the integrand is proved integrable.

Physical dot products are explicit finite coordinate sums. The kinetic expression is not
the square of the ambient supremum norm. These statements do not construct a flow or an
NS solution, and do not establish a weak NS energy identity. Concrete examples check both
time/spatial dependence and the mixed stress coefficient with nonzero gradient of divergence.

## Dirichlet Poisson result

`PDE.exists_unique_weakPoissonSolution` assumes:

- `n : ℕ`, `2 < n`;
- an open bounded `Ω ⊆ Space n`, where `Space n = Fin n → ℝ`;
- an arbitrary `f : DomainL2 Ω`, the actual L² a.e. quotient for restricted Lebesgue measure.

It produces exactly one `u : H10 Ω hΩ` satisfying, for every `v : H10 Ω hΩ`,

```text
∑ i, ∫ Ω (Dᵢu)(Dᵢv) = ∫ Ω f v.
```

`isWeakPoissonSolution_iff` exposes this integral equation.
`IsWeakPoissonSolution.norm_le` proves
`‖u‖H¹ ≤ K(Ω) ‖f‖L²`, with the finite positive constant
`K(Ω) = C(Ω)² n + 1`; `C(Ω)` is the named Mathlib Sobolev constant at p = q = 2.
No boundary smoothness is required: zero boundary is defined by H¹ closure of C∞ compact-support
functions. No trace identification, classical regularity, or dimensions one/two are asserted.
The three-dimensional example in `Checks/Examples.lean` obtains both the full integral equation
and the energy estimate from the public API.

## Integrated heat result

`PDE.exists_unique_integrated_weakHeatSolution` assumes any dimension `n`, an open `Ω`, an arbitrary
`f : DomainL2 Ω`, and a finite real `T ≥ 0`. It constructs exactly one actual Bochner a.e. class

```text
u ∈ L²([0,T]; H₀¹(Ω)),
‖u‖L²timeH¹ ≤ √(T + 1/2) ‖f‖L².
```

For every `v ∈ H₀¹(Ω)` and globally C¹ scalar time test `η` with `η(T)=0`, it proves

```text
∫₀ᵀ η′(t) (v,u(t))L² dt − ∫₀ᵀ η(t) ∫Ω ∇v·∇u(t) dt = −η(0) (f,v)L².
```

The definition `IsIntegratedWeakHeatSolution` exposes this equation as actual integrals.
`heatTimeIntegrands_integrable` separately proves that both integrands are integrable.
The two-dimensional example in `Checks/Examples.lean` uses the full equation.
Neither boundedness nor regularity of the boundary is needed for this result.

The construction includes:

- injective physical L² mass maps on finite H₀¹ trial spaces and an invertible mass operator;
- a global operator-exponential solution of each finite heat ODE;
- the exact physical energy identity and uniform L²/gradient energy bounds;
- mass projection of arbitrary L² data, best approximation, and strong convergence of initial
  projections for nested H¹-dense spaces;
- H₀¹ density in L² on every open domain;
- weak subsequence extraction in the actual Bochner L² energy space;
- passage to the integrated equation on eventual trial tests, then extension to all H₀¹ tests.

`IsIntegratedWeakHeatSolution.hasL2TimeDerivative` now proves that the L² mass trajectory,
embedded in `(H₀¹)*`, has the square-integrable weak time derivative `-B u`, where `B` is the
Dirichlet form. `dual_integrated` retains the initial datum in a Bochner identity in that dual
space; `heatDualDerivative_norm_le` bounds its norm by `‖B‖ ‖u‖L²timeH¹`.
The general `HasL2TimeDerivative` definition requires a complete normed real target space,
uses actual L² a.e. classes, and has a proved uniqueness theorem for the derivative.

`heatDualRepresentative` is continuous on `[0,T]` with values in `(H₀¹)*`, agrees a.e. with
the mass map `J*J u`, and equals the embedded initial datum at time zero. Its explicit formula is
`J*f − B ∫₀ᵗ u(s) ds`. Here `J : H₀¹ → L²` is the value map and `B` is the Dirichlet form.

`IsIntegratedWeakHeatSolution.unique` proves uniqueness as a Bochner energy-space class.
For zero initial data, the dual identity gives nonpositive energy production for the time
primitive `U(t)=∫₀ᵗ u`. Its squared physical norm is absolutely continuous and starts at zero;
thus `U=0`, and Lebesgue differentiation gives `u=0` a.e. Subtraction proves uniqueness for
arbitrary common initial data. `IsIntegratedWeakHeatSolution.norm_le` gives the displayed bound
for every solution.

For arbitrary L² initial data, a continuous physical L² representative and its initial trace
remain unproved. For H₀¹ initial data those physical results are now proved below. The exact
physical energy identity is still unproved in both cases.

## H¹-initialized heat approximations

For any finite-dimensional trial space `S ⊆ H₀¹` and `h ∈ H₀¹`,
`heatH1InitialProjection S h` is the full H¹ orthogonal projection, expressed using the existing
mass-projection API with the inherited H¹ inclusion. Its H¹ norm is at most `‖h‖H¹`.
For nested H¹-dense trial spaces, these initial projections converge strongly in H¹ and L².

`heatGalerkin_stiffness_energy_identity` tests the symmetric finite heat equation by its
physical time derivative. For the finite trajectory initialized at `hN`, it proves

```text
B(uN(T),uN(T)) + 2 ∫₀ᵀ ‖∂t(J uN)‖L²² = B(hN,hN).
```

Together with the physical mass energy, this proves contraction in the full inherited H¹ norm.
With the H¹-projected initial data, `heatH1Trajectory_norm_le` and
`heatH1Velocity_integrated_norm_sq_le` give bounds uniform in the trial dimension:

```text
‖uN(t)‖H¹ ≤ ‖h‖H¹   (t ≥ 0),
∫₀ᵀ ‖∂t(J uN)‖L²² ≤ (1/2) ‖h‖H¹².
```

`heatH1_exists_joint_weak_subsequence` constructs one common subsequence with weak limits
`u ∈ L²time H₀¹` and `d ∈ L²time L²`, retaining the bounds
`‖u‖ ≤ √T ‖h‖H¹` and `‖d‖ ≤ √(1/2) ‖h‖H¹`.
The finite velocities are actual derivatives, and their a.e. Bochner representatives are proved.
`heatH1_weak_limit_integrated_physical` now passes the physical time equation and its actual
initial term to this common limit. `heatH1_weak_limit_solves` separately passes the heat equation,
using eventual trial membership, strong convergence of the initial values, and density.

`exists_heatH1_solution_with_physical_trace` assumes any open Ω, any dimension, `h ∈ H₀¹`,
and `T ≥ 0`. It constructs an integrated weak heat solution with initial datum `J h`, its
physical time derivative `d ∈ L²time L²`, and `q : ℝ → L²(Ω)` such that

```text
HasL2TimeDerivative 0 T (J u) d,
q is continuous on [0,T],  q(0) = J h,
J u = q almost everywhere on [0,T].
```

The construction takes `q(t) = J h + ∫₀ᵗ d(s) ds` and retains both displayed Bochner norm bounds.
`IsIntegratedWeakHeatSolution.physical_trace_of_H1` transfers this regularity to every
integrated weak solution with the same H₀¹ initial datum using the proved uniqueness theorem.
This is a physical L² trace, with no assertion of pointwise-in-space regularity, an exact
energy identity, or physical time regularity for arbitrary L² initial data.

## Implemented modules

| Module | Exact implemented scope |
|---|---|
| `WeakDerivative` | Whole-space first weak coordinate derivatives; local integrability, zero, addition, scalar multiplication, a.e. uniqueness |
| `WeakDerivativeOn` | Smooth compact-support tests inside Ω; restricted integration, support/integrability lemmas, zero/add/scalar operations, a.e. invariance, restriction to smaller domains, uniqueness on open domains, whole-space compatibility |
| `ClassicalWeakDerivative` | C¹ on an open Ω implies the classical coordinate derivatives are weak derivatives, by an actual integration-by-parts theorem |
| `Sobolev` | Whole-space `MemW1p` representative predicate; zero and addition; separate from the H¹ quotient construction |
| `SobolevH1` | H¹ as the closed weak-derivative graph in the finite Hilbert product of L² a.e. classes; completeness; value/derivative continuous maps; value injectivity on open Ω; squared-norm identity; construction from L² representatives and weak derivatives |
| `SobolevZero` | Actual embedding of smooth tests in H¹, identified values/derivatives and norms; H₀¹ as the closure of their linear image; completeness; smooth approximating sequences in H¹; extension of closed conditions by density |
| `SobolevDensity` | Injective norm-decreasing H₀¹ value map with dense range in L² on every open domain, proved by smooth-test separation and orthogonal complements |
| `Poincare` | For bounded open Ω and n ≥ 3, H₀¹ Poincaré via Mathlib's smooth inequality and density; explicit comparison between the Fréchet derivative operator norm and coordinate derivatives |
| `MeanPoincare` | Mean minimizes square error; geometric interval Poincaré for AC functions with L² derivative, constant `(b-a)^2`, arbitrary endpoint values |
| `WeakIntervalPoincare` | Zero weak derivative gives the mean; actual L² weak interval identity reconstructs an AC representative without supplied trace and yields mean Poincaré |
| `ProductMeanPoincare` | L² slice and average integrability, square-energy contraction, exact variance decomposition and two-factor tensorization |
| `CubePoincare` | Unit square/cube mean L² Poincaré for ACL functions and actual line derivatives, constant 1; product measure equals ordinary restricted volume; actual H¹ geometry now proved separately by weak slicing; L⁶ now proved separately for actual H¹ |
| `IntervalTestFunctions`, `DistributionalInterval` | Compact smooth tests, zero-derivative reconstruction, Banach-valued AC representative, C¹ endpoint tests and interval mean Poincaré |
| `SobolevInterval`, `CountableTesting`, `IntervalWeakSlicing`, `ProductWeakSlicing`, `SobolevSlicing` | Actual H¹ interval geometry, common null sets for all tests and first-coordinate cylinder weak/AC slices |
| `CoordinatePermutation`, `UnitCubeCoordinates` | Actual weak partials under coordinate permutations; open cube, product measure and coordinate identifications |
| `WeakCubePoincare`, `SobolevCube` | Mean L² geometry from weak slices and the actual H¹ graph, constant one; no ACL or boundary premise |
| `IntervalWeakBound`, `CubeWeakSlices` | Unrestricted-trace W¹,¹ interval supremum bound; all-coordinate actual weak slices and measurable Fubini transfer |
| `CubeGridBound`, `WeakCubeSobolev`, `LpPower`, `WeakCubeSobolevSix` | Product-integral W¹,¹ inequality and fourth-power/Hölder estimate |
| `BoundedSmoothApproximation`, `CubeSobolevLimit` | Bounded C¹ approximations with derivative norm <= 1; Fatou removes the L⁶ premise |
| `SobolevCubeSix` | Actual H¹ L⁶ membership, translated Sobolev estimate and mean L⁶ constant 13 on the unit cube |
| `IntervalWeakChainRule` | C¹ composition of compact-test interval weak derivatives via AC reconstruction; no global Lipschitz premise |
| `LaxMilgram` | Abstract coercive variational existence/uniqueness and `‖u‖ ≤ ‖ℓ‖/α` |
| `EllipticWeakSolutions` | Bundled L² weak gradient, bounded Dirichlet form, actual coercivity derived from Poincaré, bounded L² load, concrete Poisson existence/uniqueness and energy estimate |
| `Galerkin` | Variational existence/uniqueness on complete trial subspaces (including finite-dimensional ones), orthogonality, Céa's bound against every trial approximation |
| `GalerkinConvergence` | Nested finite-dimensional spaces generated by a dense sequence; eventual approximation; strong convergence from Céa; end-to-end construction of the stationary Galerkin sequence |
| `PoissonGalerkin` | Concrete finite-dimensional Poisson approximations converging in the full H¹ norm |
| `WeakCompactness` | Every bounded sequence in a **separable complete real Hilbert space** has a subsequence converging against every inner-product test; norm bound retained, via sequential Banach–Alaoglu and Riesz |
| `SobolevCompactness` | Second-countability of domain L²; actual H₀¹ weak-subsequence extraction with no additional separability premise |
| `LinearEvolution` | Constructed global bounded-operator evolution, derivative and energy identities, accretive norm bound, and local interval uniqueness via Grönwall |
| `MassForm` | Coercivity of the actual physical mass form on any injectively embedded finite-dimensional trial space |
| `MassEvolution` | Constructed mass/stiffness evolution, actual weak equation, physical-norm energy identity and dimension-independent contraction |
| `MassHigherEnergy` | Symmetric finite mass/stiffness energy identity, continuous physical velocity, stiffness decay and integrated velocity bound |
| `MassProjection` | Physical orthogonal projection, norm contraction, orthogonality and best approximation |
| `HeatGalerkin` | Concrete homogeneous heat trajectories in arbitrary finite H₀¹ subspaces, physical mass equation, energy identity, L² and integrated gradient bounds |
| `HeatHigherEnergy` | Actual physical derivative of finite heat trajectories, exact gradient-energy dissipation, integrated derivative bound and full H¹ contraction |
| `HeatH1InitialData` | H¹-stable initial projection, best approximation and strong initial convergence; continuous finite state and velocity with uniform H¹/L² derivative bounds |
| `HeatH1Bochner` | Actual Bochner state/velocity classes, uniform norm bounds and one common weakly convergent subsequence |
| `HeatH1TimeTrace` | Physical time-L² value map; finite and limiting physical time equations with the true initial value; weak time derivative and a.e. identification with the continuous primitive |
| `HeatH1WeakLimit` | Finite velocity/stiffness equation; passage of the scalar heat equation to the H¹-initialized limit; a physical L² derivative and continuous initial trace for every weak solution with H₀¹ initial datum |
| `HeatInitialData` | Arbitrary L² initial data, uniform energy estimates, and strong convergence of initial projections for nested H¹-dense trial spaces |
| `HeatBochner` | Actual L²(0,T;H₀¹) classes of finite trajectories, uniform full H¹ norm bound, and weak subsequence extraction on every open domain |
| `TimeIntegrationByParts` | Initial-value and two-endpoint adapters to Mathlib’s vector-valued time integration by parts |
| `TimeLinearTesting` | Continuous linear spatial tests with L² time weights and passage through weak Bochner convergence |
| `TimeWeakLimit` | Justified mapped integrals and closure of the physical integrated time equation under joint weak convergence and strong initial convergence |
| `TimePairing` | Bounded bilinear time tests, integral formula, integrability, and continuity under weak Bochner convergence |
| `HeatWeakForm` | Time test L² classes, spatially continuous residual with explicit integrals and initial datum, and the integrated weak solution predicate |
| `HeatIntegratedGalerkin` | Justified time integration by parts; projected initial pairing equals the original L² datum on trial tests |
| `HeatWeakLimit` | Passage to the weak equation and initial-data term using eventual trial membership and density; end-to-end integrated heat existence |
| `WeakTimeDerivative` | Bochner L² time derivative on a finite interval, justified weighted integrals, and uniqueness as an a.e. class |
| `HeatTimeDerivative` | Actual dual-valued mass trajectory and derivative, L² derivative bound, Bochner integrated identity with the initial datum, and proved weak time differentiation |
| `TimeIntegral` | Justified Fubini exchange for Bochner integrals over the time triangle |
| `TimePrimitive` | Continuous primitive with prescribed initial value; integrated identity; a.e. identification from the weak time equation |
| `HeatDualTrace` | Continuous representative of the heat mass trajectory in `(H₀¹)*`, exact initial value, a.e. identification, and explicit spatial-form formula |
| `AbsoluteContinuity` | Increment domination, absolute continuity of normed-space primitives, bounded linear maps and squared norms; monotonicity from a.e. derivative sign |
| `PrimitiveEnergy` | Nonpositive physical energy production forces a zero-initial primitive and its L² derivative trajectory to vanish |
| `HeatUniqueness` | Subtraction, zero-data uniqueness, uniqueness for common arbitrary L² data, concrete existence/uniqueness, and the energy-space bound for every solution |
| `Mollification` | Uniform smooth approximation for uniformly continuous functions, via Mathlib; not Sobolev-norm mollification |
| `Transport` | Chain rule along a supplied differentiable curve for a time-independent scalar field |
| `VectorCalculus` | Physical coordinate dot product, divergence, advection, tensor divergence, Laplacian; scalar product/sum rules and directional-derivative decomposition |
| `MaterialDerivative` | Actual time-dependent material chain rule from joint differentiability along a supplied trajectory |
| `ContinuityEquation` | Conservative/material residual equality and mass-equation equivalence; nonzero materially constant density implies zero divergence under mass conservation |
| `MomentumForms` | Conservative momentum equals density times material acceleration plus velocity times the mass residual; momentum equation equivalence under continuity, including vacuum |
| `NewtonianStress` | C² mixed coordinate derivative symmetry; divergence of constant-viscosity Newtonian stress and the divergence-free Laplacian corollary |
| `IncompressibleEnergy` | C¹ compact-support scalar transport integration by parts, actual integrability, kinetic chain rule, and divergence-free convection cancellation on whole space |

## Open portions of the roadmap

- General W^{k,p} quotient spaces and completeness; higher/vector weak derivatives.
- Convolution commutation and Lᵖ/Sobolev convergence; general trace/extension machinery.
- General-domain distributional-H¹ mean Poincaré and further Sobolev embeddings;
  interval, unit-square/cube L² geometry and actual H¹ cube L⁶ estimates are proved.
- Uniformly elliptic variable coefficients, interior and boundary regularity.
- Rellich–Kondrachov; the physical heat energy identity; physical L² representatives and initial
  traces for arbitrary L² data; forcing and more general parabolic equations.
- Construction of time-dependent flows, continuity/transport solutions, entropy and shock formation.
- Fluid calculus for weak solutions and boundary traces, variable-viscosity stress,
  closed compressible local theory and low-Mach convergence.

The M1 Sobolev and M2 elliptic milestones have substantial completed parts; their full roadmaps
are still active. The Poisson core of M2 is complete in the stated dimension range.
M3 now includes actual finite heat ODEs, uniform energy bounds, weak Bochner limits and the
integrated heat existence/uniqueness result above, with a dual-space time trace.
The physical L² trace for H₀¹ initial data is checked. The exact energy identity and extension
of that physical trace to arbitrary L² initial data remain active.
The reference submodule remains separate and unmodified.

## Conventions and verification limits

- Equality of L² elements is a.e. equality; weak derivatives are unique a.e. on open domains.
- Smooth tests use `ContDiff ℝ ∞`; local integrability/support justify the weak pairings.
- H¹ uses the sum of squared L² component norms. The PDE proof controls this full norm by gradient
  energy; it does not replace the topology with an unproved gradient norm.
- The heat ODE uses the physical L² mass pairing. Finite-dimensional mass coercivity constants
  may depend on the trial space; the proved physical energy estimates do not.
- The heat weak-limit proof uses linear time tests and Hilbert weak compactness. It does not
  assert Rellich compactness, strong convergence of the trajectories, or uniform H⁻¹ bounds
  for the time derivatives of arbitrary trial projections.
- `MemW1p` permits all exponents as a predicate; no general p Banach-space theorem follows from it.
- Some nested Sobolev type inference needs the local elaboration option
  `backward.isDefEq.respectTransparency false`; selected statements have a larger heartbeat allowance.
  These change elaboration only, with all resulting proofs checked by Lean's kernel.
- No `sorry`, added axiom, native proof shortcut, or suppressed proof warning is used.
- The reference is not imported/built. No independent kernel replay or remote CI run is claimed.
- Low-Mach preterminal convergence, fixed-positive-Mach blowup, and terminal-time convergence
  remain separate obligations; this library proves none of those fluid research conclusions.
