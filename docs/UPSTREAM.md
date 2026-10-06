# Reference source audit

Reference: <https://github.com/weiran-sun/pde>

- Pinned commit: `0ab5d79a0d7ad10deeb48b033c0025311214dc5c`.
- Commit date: 2026-06-21; subject: `Rename weak_derivative.lean to WeakDerivative.lean`.
- Location: `references/weiran-sun-pde`, an ordinary Git submodule with the public upstream URL.
- License: Apache-2.0; the upstream license and history remain in the submodule.
- The upstream README names Rustom Choksi, *Partial Differential Equations, A First Course*.
  This Evans companion is a separate project with a different organization and toolchain.

## Relevant source files

| Reference module | Candidate value |
|---|---|
| `PDE/Basics/Heat/HeatKernel.lean` | Fundamental heat kernel |
| `PDE/Basics/Heat/HeatSolution.lean` | Convolution solution |
| `PDE/Basics/Heat/HeatSolutionProperty.lean` | Solution properties |
| `PDE/Basics/Heat/HeatMaximumPrinciple.lean` | Maximum principle |
| `PDE/SobolevSpace/LpFunctionSpaces.lean` | Local `Lᵖ` and test-function setup |
| `PDE/SobolevSpace/WeakDerivative.lean` | Weak multi-derivatives, uniqueness, linear structure |
| `PDE/SobolevSpace/SobolevSpaces.lean` | `W^{k,p}` construction |
| `PDE/SobolevSpace/HkSpaces.lean` | Hilbert/Sobolev direction |

## Compatibility findings from source inspection

1. Upstream pins Lean and Mathlib `v4.30.0`; this project pins `v4.34.0-rc2`.
2. Upstream `PDE.lean` and Sobolev sources still import names such as
   `PDE.SobolevSpace.Lp_function_spaces` and `PDE.SobolevSpace.weak_derivative`, while the
   tracked files are now `LpFunctionSpaces.lean` and `WeakDerivative.lean`.
   These import paths do not match on a case-sensitive filesystem.
3. Upstream sets `-Dwarn.sorry=false`. A textual scan of the checked-out `PDE/` and `Lemmas/`
   Lean sources found no `sorry` or `axiom` tokens, but that scan is not a kernel audit.
   The new project does not inherit this suppression option.
4. Upstream has extra documentation/extractor dependencies. They are not needed for this
   companion's mathematical library.
5. Both projects use a `PDE` import root. Importing both unchanged into a single Lake
   workspace would require deliberate namespace/module-path work.

The reference was inspected, not built under its own toolchain. These findings do not claim
that its mathematical arguments are false. Its modules are not in the local proof dependency
graph and are not counted in local verification.

## Porting policy

Keep the reference checkout pinned and unchanged. Before moving a candidate into the active
library, audit its definitions and dependencies, preserve attribution for adapted code,
update imports for the pinned Mathlib, build it, and check its transitive axioms. Document
any difference between its statement and the target interface. Prefer extending Mathlib's
existing interfaces where practical.
