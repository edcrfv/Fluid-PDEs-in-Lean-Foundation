#!/usr/bin/env python3
"""Build the library and check the transitive axioms of its public theorem roots."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main():
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    logs = ROOT / "logs" / timestamp
    logs.mkdir(parents=True, exist_ok=True)
    sources = (sorted(ROOT.glob("PDE/**/*.lean")) + sorted(ROOT.glob("Checks/**/*.lean"))
               + [ROOT / "scripts/lean-limited.py",
                  ROOT / "scripts/limited-toolchain.py", ROOT / "scripts/env.sh",
                  ROOT / "scripts/verify.py", ROOT / "scripts/check.sh"]
               + [ROOT / "PDE.lean", ROOT / "Checks.lean", ROOT / "lakefile.toml",
                  ROOT / "lake-manifest.json", ROOT / "lean-toolchain"])
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    expected = re.findall(r"^#print axioms (\S+)$", (ROOT / "Checks/Axioms.lean").read_text(), re.M)
    report = {"checked_at_utc": timestamp, "status": "failed", "source_sha256": hashes,
              "scope": "Shared PDE foundation and four example modules; all retained named public roots have transitive Lean axiom audits. Independent replay is not included.",
              "build_targets": ["PDE", "Checks"],
              "independent_kernel_replay": False, "allowed_axioms": sorted(ALLOWED), "commands": []}
    try:
        for index, command in enumerate([
            ["lake", "env", "lean", "--version"],
            ["lake", "build", "PDE", "Checks"],
            ["lake", "env", str(ROOT / "scripts/lean-limited.py"), "-DwarningAsError=true", "Checks/Axioms.lean"],
        ]):
            print("Running: " + " ".join(command), flush=True)
            result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, timeout=None if index == 1 else 600)
            (logs / f"{index}.log").write_text(result.stdout)
            print(result.stdout, end="", flush=True)
            report["commands"].append({"argv": command, "exit_code": result.returncode,
                                       "log": str((logs / f"{index}.log").relative_to(ROOT))})
            if result.returncode:
                raise RuntimeError(f"Command failed with exit {result.returncode}")
            if index == 0 and "version 4.34.0-rc2" not in result.stdout:
                raise RuntimeError("Unexpected Lean version")
            if index == 2:
                found = {}
                for name, dependencies in re.findall(
                    r"'([^\n]+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout
                ):
                    found[name] = [x.strip() for x in dependencies.split(",") if x.strip()]
                for name in re.findall(r"'([^\n]+)' does not depend on any axioms", result.stdout):
                    found[name] = []
                if set(found) != set(expected):
                    raise RuntimeError(f"Axiom output mismatch: expected {expected}, got {list(found)}")
                for name, axioms in found.items():
                    if set(axioms) - ALLOWED:
                        raise RuntimeError(f"Disallowed axioms in {name}: {axioms}")
                report["theorems"] = found
        if any(hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != digest
               for name, digest in hashes.items()):
            raise RuntimeError("Source changed during verification")
        report["status"] = "passed"
    except (RuntimeError, subprocess.SubprocessError, OSError) as error:
        report["error"] = str(error)
    finally:
        (ROOT / "reports").mkdir(exist_ok=True)
        output = json.dumps(report, indent=2) + "\n"
        (ROOT / "reports/latest.json").write_text(output)
        (logs / "verification.json").write_text(output)
    print(f"Verification {report['status']}: reports/latest.json", flush=True)
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())
