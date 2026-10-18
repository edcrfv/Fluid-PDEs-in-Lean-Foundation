# Fluid PDEs in Lean — Foundation

A reusable Lean 4 foundation for analysis of partial differential equations,
organized around the Sobolev, elliptic and linear evolution material in
Lawrence C. Evans, *Partial Differential Equations*, second edition.

This is a foundation-only distribution of
[Fluid-PDEs-in-Lean](https://github.com/edcrfv/Fluid-PDEs-in-Lean).
It contains the shared `PDE/` library, examples, verification scripts and
foundation documentation. Research projects and their Git history are excluded.
See [provenance](docs/PROVENANCE.md) and [license scope](LICENSING.md).

## Mathematical scope

The library provides open-domain weak derivatives and actual H¹/H₀¹ spaces;
Poincaré and selected cube Sobolev estimates; a concrete Dirichlet Poisson
existence/uniqueness result in dimensions at least three; Galerkin constructions;
integrated weak heat existence/uniqueness and a physical L² trace for H₀¹ initial
data; interior C∞ regularity of locally integrable distributional heat solutions
on arbitrary open domains; and smooth fluid calculus identities.

[Implementation status](docs/STATUS.md) records the hypotheses and limitations.
Some modules contain documentation of planned results, so an import is not
evidence that the theorem named in a module has been proved. In particular,
Rellich compactness and fluid existence/blowup results are not claimed.

## Install and verify

Install [elan](https://github.com/leanprover/elan) and open the repository in
VS Code with the Lean 4 extension. The committed toolchain and manifest pin:

- Lean: `leanprover/lean4:v4.34.0-rc2`
- Mathlib: `85e3a25e006c35636f0e53b0e9296caca2685bc0`

From the repository root, run:

```bash
lake exe cache get
bash scripts/check.sh
```

`lake build` also builds both default targets, `PDE` and `Checks`.
The check script builds the shared library and five example modules with warnings
as errors, then audits the transitive axioms of all 560 current public roots.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed. It records source
hashes and rejects source changes during verification. This is a Lean kernel
build and named-root axiom audit, not an independent kernel replay.

Results are written to `reports/latest.json` and `logs/<UTC timestamp>/`.
The GitHub Actions workflow runs the same check.

The local check environment permits one Lean compiler at a time, with two
threads, a 3000 MiB Lean memory limit and a 3500 MiB build-tree RSS watchdog.
The watchdog leaves headroom below the requested 4 GB local-work budget; on macOS
it samples process memory rather than imposing a hard operating-system limit.
For direct compiler checks, source `scripts/env.sh` in Bash and use
`lake env "$LEAN" file.lean`; `lake env lean` can bypass the wrapper through PATH.
The initial standalone snapshot passed on 2026-10-06; its
[verification report](reports/foundation-verification.json) and logs are retained.

To inspect the separate, pinned reference source:

```bash
git submodule update --init
```

The reference submodule is not imported or built by this library.

For an offline setup with an existing matching dependency cache, the optional
`scripts/bootstrap-local.py /path/to/.lake/packages` checks dependency revisions
and source cleanliness before copying them into this checkout. It creates no
runtime dependency on the source checkout.

## Contribute

Search the [pinned Mathlib inventory](docs/MATHLIB.md) and
[reference inventory](docs/UPSTREAM.md) first. Follow [AGENTS.md](AGENTS.md):
preserve exact mathematical hypotheses, avoid unfinished proof shortcuts, add
new public roots to `Checks/Axioms.lean`, update the status inventory, and run
`bash scripts/check.sh`.

See the [roadmap](docs/ROADMAP.md),
[smooth fluid scope](docs/SMOOTH_FLUID.md), and
[remaining physical time-trace work](docs/TIME_TRACE_NEXT.md).
