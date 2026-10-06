# Evans PDE foundation roadmap

Primary reference: Lawrence C. Evans, *Partial Differential Equations*, second
edition, Graduate Studies in Mathematics 19, AMS, 2010. This is a dependency-driven
companion to Chapters 5–7, not a complete transcription of the textbook.

## Current foundation

The exact scope is recorded in [STATUS.md](STATUS.md): open-domain weak derivatives;
complete H¹ and H₀¹; smooth density in H₀¹; selected Poincaré and cube Sobolev
inequalities; variational Poisson existence/uniqueness; stationary and heat Galerkin
constructions; integrated weak heat existence/uniqueness; dual time traces and
physical L² traces for H₀¹ initial data; smooth fluid calculus identities.

## Next foundations

1. General integer-order W^{k,p} spaces, higher/vector weak derivatives and completeness.
2. Sobolev-norm mollification, convolution/derivative compatibility, trace and extension theory.
3. General-domain mean Poincaré and additional Sobolev embeddings; Rellich compactness.
4. Exact physical heat energy identity and physical L² time traces for arbitrary L² data;
   forcing and more general parabolic equations. See [TIME_TRACE_NEXT.md](TIME_TRACE_NEXT.md).
5. Variable-coefficient elliptic equations, interior and boundary regularity.
6. Weak transport/continuity interfaces and fluid energy/boundary calculus.

These are plans, not placeholder theorems or claims of completed fluid applications.

## Completion rule

Search pinned Mathlib and the reference inventory, state exact mathematical
hypotheses, implement a checked proof, add public audit roots and relevant
examples, update the scope inventory, and run `bash scripts/check.sh`.
An assumed conclusion or a successfully imported outline does not meet this rule.
