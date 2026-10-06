import PDE.Sobolev
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

/-!
# Existing smooth Sobolev inequalities; planned weak-space extension

Mathlib already proves Gagliardo–Nirenberg–Sobolev inequalities for smooth compactly
supported functions, including `eLpNorm_le_eLpNorm_fderiv`.
Extending these to the local `MemW1p` interface requires an approximation theorem.
Bounded-domain embeddings and boundary extension operators are not established here.
-/
