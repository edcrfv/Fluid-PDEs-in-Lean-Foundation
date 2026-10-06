#!/usr/bin/env python3
"""Expose a standard toolchain layout whose compiler runs through our limiter.

Lake 4.34 uses LEAN to discover a sysroot, then executes sysroot/bin/lean.
Setting LEAN alone therefore does not wrap compiler jobs.
"""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]

def prepare(real):
    actual = Path(subprocess.check_output([real, '--print-prefix'], text=True).strip()).resolve()
    target = ROOT / '.tools/limited-lean'
    target.mkdir(parents=True, exist_ok=True)
    (target / 'bin').mkdir(exist_ok=True)
    def link(path, source):
        if path.is_symlink() and path.resolve() == source.resolve():
            return
        if path.exists() and not path.is_symlink():
            raise RuntimeError('Refusing to replace an existing toolchain file: ' + str(path))
        if path.is_symlink():
            path.unlink()
        path.symlink_to(source, target_is_directory=source.is_dir())
    for entry in actual.iterdir():
        if entry.name != 'bin':
            link(target / entry.name, entry)
    for entry in (actual / 'bin').iterdir():
        if entry.name != 'lean':
            link(target / 'bin' / entry.name, entry)
    link(target / 'bin/lean', ROOT / 'scripts/lean-limited.py')
    return target

if __name__ == '__main__':
    print(prepare(sys.argv[1]))
