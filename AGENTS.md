# Fluid PDEs in Lean — Foundation

Develop the reusable Evans PDE foundation in this repository.
Keep implemented scope explicit in `docs/ROADMAP.md` and `docs/STATUS.md`.

- Keep Lean and Mathlib pinned. The reference submodule remains separate and unmodified.
- Search pinned Mathlib and the reference inventory before duplicating infrastructure.
- Do not claim a theorem from an import, module name, outline or assumed conclusion.
- Do not use `sorry`, new axioms, `native_decide`, unsafe proof shortcuts or warning suppression.
- Preserve a.e. versus pointwise equality, domain, solution class, regularity and bound direction.
- Put unimplemented results in documentation, not placeholder theorem statements.
- Add new public theorem roots to `Checks/Axioms.lean`, update the status inventory,
  and run `bash scripts/check.sh` after mathematical changes.
- Use ordinary Lake dependencies or verified local cache copies.
- Preserve Apache-2.0 attribution and the original MIT notice; see `LICENSING.md`.
- External publication and messages require an explicit user instruction.
