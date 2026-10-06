#!/usr/bin/env bash
# Shared repository environment; never resolves a sibling workspace.
PDE_REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if [[ -x "$PDE_REPO_ROOT/.tools/lean/bin/lake" ]]; then
  export PATH="$PDE_REPO_ROOT/.tools/lean/bin:$PATH"
elif [[ -x "${ELAN_HOME:-$HOME/.elan}/bin/lake" ]]; then
  export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
fi
if ! command -v lake >/dev/null 2>&1; then
  echo 'Install elan and the pinned lean-toolchain, or run bootstrap-tools.py --from-workspace once.' >&2
  return 1
fi
export PDE_REPO_ROOT
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
if [[ "${PDE_LIMIT_COMPILERS:-0}" == 1 ]]; then
  PDE_REAL_LEAN="$(command -v lean)"
  export PDE_REAL_LEAN
  export LEAN="$PDE_REPO_ROOT/scripts/lean-limited.py"
  export LAKE_OVERRIDE_LEAN=true
  LEAN_SYSROOT="$(python3 "$PDE_REPO_ROOT/scripts/limited-toolchain.py" "$PDE_REAL_LEAN")" || return 1
  export LEAN_SYSROOT
fi
