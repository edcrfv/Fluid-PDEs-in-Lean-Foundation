import PDE.HeatUniqueness
import PDE.HeatH1WeakLimit

/-!
# Parabolic energy entrypoint

The imports construct finite-dimensional heat Galerkin solutions with the L² mass
pairing and Dirichlet stiffness form, prove the exact energy identity, and bound the
energy uniformly in the trial dimension for arbitrary L² initial data. The initial
projections converge strongly when the trial spaces are nested and H¹-dense.
Weak Bochner subsequence extraction and density then produce an infinite-dimensional
solution of the time-integrated equation with its initial datum. Its dual-valued L²
time derivative, continuous dual representative and dual initial trace are proved.
An energy argument through a time primitive proves uniqueness in the Bochner energy
space. H¹-projected initial data now have uniform full H¹ state and physical L² velocity
estimates from the symmetric stiffness identity, with simultaneous weak subsequence extraction.
Passing both equations to that limit proves the physical L² time derivative, continuous
representative and initial trace for H₀¹ initial data. The physical energy identity and the
physical trace for arbitrary L² initial data remain to be proved.
-/
