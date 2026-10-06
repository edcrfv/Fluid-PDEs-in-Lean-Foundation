#!/usr/bin/env bash
set -euo pipefail
PDE_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$PDE_ROOT"

export PDE_LIMIT_COMPILERS=1
source "$PDE_ROOT/scripts/env.sh"
python3 scripts/verify.py
