#!/usr/bin/env python3
"""Copy a matching, already-built dependency cache without modifying its source."""
import argparse
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("packages", type=Path, help="Existing .lake/packages directory")
    args = parser.parse_args()
    source = args.packages.resolve()
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    # Validate every revision before copying any dependency.
    for package in manifest["packages"]:
        path = source / package["name"]
        rev = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
        if rev != package["rev"]:
            raise SystemExit(f"Revision mismatch for {package['name']}: {rev}")
        dirty = subprocess.check_output(
            ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"], text=True
        ).strip()
        if dirty:
            raise SystemExit(f"Tracked changes in source dependency {package['name']}; refusing copy")
        if (ROOT / ".lake/packages" / package["name"]).exists():
            raise SystemExit(f"Destination already exists: {package['name']}; use a fresh cache")
    destination = ROOT / ".lake/packages"
    destination.mkdir(parents=True, exist_ok=True)
    for package in manifest["packages"]:
        name = package["name"]
        print(f"Copying pinned {name} (reflink where supported)", flush=True)
        subprocess.run(["cp", "-a", "--reflink=auto", str(source / name), str(destination / name)], check=True)
    print("Local dependency copies ready. The source dependencies were not changed.")


if __name__ == "__main__":
    main()
