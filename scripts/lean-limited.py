#!/usr/bin/env python3
"""One compiler, 3000 MiB Lean budget, and a 3500 MiB build-tree RSS watchdog.

The RSS watchdog leaves headroom below the user's 4 GB local-work budget.
On macOS this is a sampled guard, not an operating-system memory reservation.
"""
import fcntl
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]

def process_table():
    output = subprocess.check_output(['ps', '-axo', 'pid=,ppid=,rss=,comm='], text=True)
    return {int(pid): (int(parent), int(rss), name)
            for line in output.splitlines()
            for pid, parent, rss, name in [line.split(None, 3)]}

def build_root(table):
    """Include Lake and all queued compilers in the memory accounting."""
    root = current = os.getpid()
    while current in table:
        parent, _, name = table[current]
        if Path(name).name == 'lake':
            root = current
        if parent == current:
            break
        current = parent
    return root

def tree_rss(table, root):
    descendants = {root}
    while True:
        expanded = descendants | {pid for pid, (parent, _, _) in table.items()
                                  if parent in descendants}
        if expanded == descendants:
            return sum(table[pid][1] for pid in descendants if pid in table)
        descendants = expanded

def main():
    real = os.environ.get('PDE_REAL_LEAN')
    if not real or Path(real).resolve() == Path(__file__).resolve():
        raise SystemExit('PDE_REAL_LEAN must identify the actual pinned compiler')
    if any(x in sys.argv[1:] for x in ['--version', '--print-prefix', '--print-libdir', '--githash', '--help']):
        os.execv(real, [real, *sys.argv[1:]])
    locks = ROOT / '.locks/compiler'
    locks.mkdir(parents=True, exist_ok=True)
    slots = [(locks / 'slot-0').open('a')]
    start = time.monotonic()
    chosen = None
    while chosen is None:
        for slot in slots:
            try:
                fcntl.flock(slot, fcntl.LOCK_EX | fcntl.LOCK_NB)
                chosen = slot
                break
            except BlockingIOError:
                pass
        if chosen is None:
            if time.monotonic()-start > 600:
                raise SystemExit('Timed out waiting for a compiler slot')
            time.sleep(.05)
    command = [real, *sys.argv[1:], '-j2', '-M3000']
    # Optional Linux CPU scope; ordinary local/CI checks use the portable limiter.
    if os.environ.get('PDE_COMPILER_SCOPE') == '1':
        command = ['systemd-run', '--user', '--scope', '--quiet',
                   '--unit', f'fluid-lean-{os.getpid()}', '-p', 'CPUQuota=200%',
                   '-p', 'MemoryMax=3G', '-p', 'MemorySwapMax=0', *command]
    root = build_root(process_table())
    proc = subprocess.Popen(command, start_new_session=True)
    def stop(*_):
        if proc.poll() is None:
            try:
                os.killpg(proc.pid, signal.SIGTERM)
            except ProcessLookupError:
                proc.wait()
                return
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    try:
        deadline = time.monotonic() + 600
        while proc.poll() is None:
            if tree_rss(process_table(), root) >= 3500 * 1024:
                print('Stopping Lean: build-tree RSS reached the 3500 MiB guard.', file=sys.stderr)
                stop()
                return 137
            if time.monotonic() >= deadline:
                stop()
                return 124
            try:
                return proc.wait(timeout=.2)
            except subprocess.TimeoutExpired:
                pass
        return proc.returncode
    except subprocess.TimeoutExpired:
        stop()
        return 124
    finally:
        stop()
        for slot in slots:
            slot.close()

if __name__ == '__main__':
    sys.exit(main())
