#!/usr/bin/env python3
"""Compile the documented heat regularity statement and its proof application."""

from pathlib import Path
import os
import re
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def main():
    if not os.environ.get("PDE_REAL_LEAN"):
        # Preserve standalone invocation while using the same memory limiter as check.sh.
        os.execv("/bin/bash", ["bash", "-c",
            'export PDE_LIMIT_COMPILERS=1; source "$1/scripts/env.sh" && '
            'exec "$2" "$1/scripts/check-heat-interior-statement.py"',
            "heat-statement-check", str(ROOT), sys.executable])
    document = ROOT / "docs/HEAT_INTERIOR_REGULARITY.md"
    blocks = re.findall(r"^```lean\n(.*?)^```", document.read_text(), re.M | re.S)
    if len(blocks) != 1:
        raise SystemExit("Expected exactly one Lean theorem example block")
    subprocess.run(["lake", "build", "PDE.HeatInteriorRegularity"], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory(prefix="heat-interior-statement-") as temporary:
        source = Path(temporary) / "HeatInteriorStatement.lean"
        source.write_text(blocks[0])
        subprocess.run(
            ["lake", "env", str(ROOT / "scripts/lean-limited.py"), "-DautoImplicit=false",
             "-DwarningAsError=true", str(source)],
            cwd=ROOT, check=True,
        )
    print("Documented interior regularity statement and proof application passed.")


if __name__ == "__main__":
    main()
