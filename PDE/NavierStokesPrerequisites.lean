import PDE.RellichKondrachov
import PDE.EllipticWeakSolutions
import PDE.ParabolicEnergy
import PDE.Transport
import PDE.MaterialDerivative
import PDE.ContinuityEquation
import PDE.MomentumForms
import PDE.NewtonianStress
import PDE.IncompressibleEnergy

/-!
# Dependency entrypoint for fluid PDE applications

This module collects the Sobolev/variational foundation and proved smooth fluid
identities: the material chain rule, mass and momentum form conversions,
constant-viscosity stress divergence, and compact-support energy cancellation.
It proves no
Navier–Stokes existence, blowup, or low-Mach convergence theorem. See `docs/ROADMAP.md`
for the missing bridges and `docs/STATUS.md` for the exact implemented scope.
-/
