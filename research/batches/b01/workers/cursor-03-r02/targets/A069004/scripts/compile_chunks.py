#!/usr/bin/env python3
"""Compile independent A069004 certificate/count files, two at a time."""

from __future__ import annotations

import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path("/workspace/research/batches/b01/workers/cursor-03-r02/targets/A069004")
LOG = ROOT / "compile.log"
JOBS = 2


def files() -> list[Path]:
    xs = sorted(ROOT.glob("C[0-9]*.lean"), key=lambda p: int(p.stem[1:]))
    xs += sorted(ROOT.glob("Count[0-9]*.lean"))
    return xs


def up_to_date(src: Path) -> bool:
    olean = src.with_suffix(".olean")
    if not olean.exists():
        return False
    core = ROOT / "Core.olean"
    if not core.exists():
        return False
    ot = olean.stat().st_mtime
    return ot >= src.stat().st_mtime and ot >= core.stat().st_mtime


def compile_one(src: Path) -> tuple[str, int, float, str]:
    olean = src.with_suffix(".olean")
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "2"
    t0 = time.time()
    r = subprocess.run(
        [
            "lake",
            "env",
            "lean",
            "-DwarningAsError=true",
            "-R",
            str(ROOT),
            "-o",
            str(olean),
            str(src),
        ],
        cwd="/workspace",
        capture_output=True,
        text=True,
        env=env,
    )
    dt = time.time() - t0
    out = (r.stdout or "") + (r.stderr or "")
    return src.name, r.returncode, dt, out[-4000:]


def main() -> int:
    xs = files()
    todo = [p for p in xs if not up_to_date(p)]
    skipped = len(xs) - len(todo)
    LOG.write_text(f"compile {len(todo)}/{len(xs)} files jobs={JOBS} skip={skipped}\n")
    fails = 0
    done = 0
    if todo:
        with ThreadPoolExecutor(max_workers=JOBS) as ex:
            futs = [ex.submit(compile_one, p) for p in todo]
            for fut in as_completed(futs):
                name, code, dt, tail = fut.result()
                done += 1
                status = "OK" if code == 0 else "FAIL"
                line = f"[{done}/{len(todo)}] {status} {name} {dt:.1f}s\n"
                print(line, end="", flush=True)
                with LOG.open("a") as fh:
                    fh.write(line)
                    if code != 0:
                        fh.write(tail + "\n")
                        fails += 1
    with LOG.open("a") as fh:
        fh.write(f"fails {fails}\n")
    print("fails", fails)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
