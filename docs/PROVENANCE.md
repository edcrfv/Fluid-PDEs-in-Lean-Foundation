# Foundation distribution provenance

Source: [edcrfv/Fluid-PDEs-in-Lean](https://github.com/edcrfv/Fluid-PDEs-in-Lean).
Snapshot: `526f24acab7993b8efbe322ba33811657bd6d79a`.

All 120 files under `PDE/`, the `PDE.lean` entrypoint, and four independent
foundation example modules are copied byte-for-byte from this source snapshot.
The 478 `#print axioms PDE.…` roots are retained in their source order.
No PDE theorem statement or proof is changed by this distribution.

The original Evans foundation entered the source repository at `7aa8f31`;
its Apache-2.0 license and the original destination MIT notice are preserved.
The reference submodule remains pinned to
`0ab5d79a0d7ad10deeb48b033c0025311214dc5c` at its public upstream URL.

Distribution changes:

- Exclude the entire research-project directory and all project-dependent checks.
- Start a fresh Git repository with no parent repository history.
- Build only `PDE` and foundation `Checks`, with the original Lean/Mathlib pins.
- Remove project-only NavierStokesAndEuler, lean4export and Comparator dependencies.
- Scope verification and CI to shared sources, four examples and 478 public roots.
- Retain relevant foundation documentation; rewrite the overview, roadmap and
  license scope for this distribution.
- Exclude research reports, campaign automation, manuscript tooling, local caches
  and the parent repository's Git metadata.

Run `bash scripts/check.sh` for a verification report bound to this distribution's
actual source hashes. Parent-workspace verification reports are not copied as
evidence for this snapshot. Independent kernel replay is not claimed.
