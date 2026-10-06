#!/usr/bin/env python3
"""Lake's Lean subprocess: two slots, four threads, 600 seconds per compiler."""
import fcntl
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]

def main():
    real = os.environ.get('PDE_REAL_LEAN')
    if not real or Path(real).resolve() == Path(__file__).resolve():
        raise SystemExit('PDE_REAL_LEAN must identify the actual pinned compiler')
    if any(x in sys.argv[1:] for x in ['--version', '--print-prefix', '--print-libdir', '--githash', '--help']):
        os.execv(real, [real, *sys.argv[1:]])
    locks = ROOT / '.locks/compiler'
    locks.mkdir(parents=True, exist_ok=True)
    slots = [(locks / f'slot-{i}').open('a') for i in range(2)]
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
    command = [real, '-j4', *sys.argv[1:]]
    # Optional Linux CPU scope; ordinary local/CI checks use the portable limiter.
    if os.environ.get('PDE_COMPILER_SCOPE') == '1':
        command = ['systemd-run', '--user', '--scope', '--quiet',
                   '--unit', f'fluid-lean-{os.getpid()}', '-p', 'CPUQuota=400%',
                   '-p', 'MemoryMax=infinity', '-p', 'MemorySwapMax=infinity', *command]
    proc = subprocess.Popen(command, start_new_session=True)
    def stop(*_):
        if proc.poll() is None:
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    try:
        return proc.wait(timeout=600)
    except subprocess.TimeoutExpired:
        stop()
        return 124
    finally:
        for slot in slots:
            slot.close()

if __name__ == '__main__':
    sys.exit(main())
