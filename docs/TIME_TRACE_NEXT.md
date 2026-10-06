# Remaining physical L² time trace

Checked: the integrated heat solution is unique in `L²(0,T;H₀¹)`, has a dual-valued L² time
derivative, and has a continuous `(H₀¹)*` mass representative with the correct initial value.
`TimePrimitive` reconstructs continuous representatives in any complete normed real space;
`AbsoluteContinuity` and `PrimitiveEnergy` supply the energy tools.

Also checked: for H₀¹ initial data, the physical weak derivative, continuous physical L²
representative and initial trace, with actual passage through both limiting equations.

Still required: the exact physical energy identity, then a continuous **physical L²**
representative and initial trace for arbitrary L² initial data. Dual continuity alone is insufficient.

## A concrete construction route

1. **Checked:** use initial data `h ∈ H₀¹`. Project it to nested dense trial spaces in the **H¹ norm**,
   so the initial H¹ norms are uniformly bounded and the initial projections converge in H¹.
   The existing physical L² mass projections do not have a proved H¹ stability bound.
2. **Checked:** test each finite heat ODE by its time derivative. Symmetry of the Dirichlet form yields
   `∫₀ᵀ ‖uN′‖L²² ≤ 1/2 ‖∇hN‖L²²`. Together with the existing energy estimate this gives a
   bounded pair in `L²time H₀¹ × L²time L²`.
3. **Checked:** pass both the heat equation and the physical time integration-by-parts identity
   on that common subsequence. Initial H¹ convergence supplies the correct L² datum.
   Apply `TimePrimitive` in physical L² to obtain a continuous, absolutely continuous
   representative for these H₀¹ initial data.
4. Use its physical derivative and heat equation to prove the exact energy identity and
   contraction for differences of such solutions.
5. Approximate an arbitrary L² datum by H₀¹ data, using the proved `H10.value_denseRange`.
   The difference estimate should give uniform Cauchy convergence of the physical representatives
   and strong Cauchy convergence in `L²time H₀¹`. Pass to the continuous L² representative,
   initial value and energy identity. Integrated uniqueness identifies it with the existing solution.

`MassHigherEnergy`, `HeatHigherEnergy`, `HeatH1InitialData`, and `HeatH1Bochner` implement
steps 1–2 and the joint extraction in step 3. `TimeWeakLimit`, `HeatH1TimeTrace` and
`HeatH1WeakLimit` complete passage through both equations and the physical trace in step 3. The common subsequence is obtained by two
successive Hilbert extractions, avoiding a choice of norm on a product space. The remaining
steps are a plan, not an implemented theorem. A general energy-space time-trace theorem
for a Hilbert triple would be another route if suitable reusable machinery is developed.

## Next implementation details

- Prove that bounded linear maps preserve `HasL2TimeDerivative`. Map the physical derivative
  into the dual energy space and use derivative uniqueness to identify it with `-B u`.
  This gives a single a.e. identity of spatial functionals, allowing evaluation at `u(t)`.
- Establish absolute continuity and a.e. differentiation of the physical primitive. Combine
  its squared-norm derivative with the heat equation and the justified integrals to obtain
  the exact energy identity and contraction in the physical initial L² norm.
- Use those difference estimates on an H₀¹ approximation to arbitrary L² initial data;
  prove uniform convergence of physical representatives and the strong energy-space limit.

The finite projected initial term and physical derivative identification no longer need to
be reproved: `heatH1_integrated_physical`, `heatH1_weak_limit_integrated_physical`,
`heatH1_weak_limit_solves`, and `IsIntegratedWeakHeatSolution.physical_trace_of_H1` supply them.
