#!/usr/bin/env python3
"""Compile GlueCert, GlueCount, A069004.lean, and TypeMatch after chunks."""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

ROOT = Path("/workspace/research/batches/b01/workers/cursor-03-r02/targets/A069004")
LEAN_DIR = ROOT / "lean"
LOG = ROOT / "glue.log"


def run(src: Path, olean: Path | None) -> int:
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "2"
    cmd = [
        "lake",
        "env",
        "lean",
        "-DwarningAsError=true",
        "-R",
        str(ROOT),
    ]
    if olean is not None:
        cmd += ["-o", str(olean)]
    cmd.append(str(src))
    print("compile", src.name, flush=True)
    r = subprocess.run(cmd, cwd="/workspace", env=env)
    line = f"{src.name} exit={r.returncode}\n"
    print(line, end="", flush=True)
    with LOG.open("a") as fh:
        fh.write(line)
    return r.returncode


def main() -> int:
    LEAN_DIR.mkdir(parents=True, exist_ok=True)
    LOG.write_text("glue compile\n")
    jobs = [
        (ROOT / "GlueCert.lean", LEAN_DIR / "GlueCert.olean"),
        (ROOT / "GlueCount.lean", LEAN_DIR / "GlueCount.olean"),
        (ROOT / "A069004.lean", LEAN_DIR / "A069004.olean"),
        (ROOT / "TypeMatch.lean", None),
    ]
    for src, olean in jobs:
        if run(src, olean) != 0:
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
