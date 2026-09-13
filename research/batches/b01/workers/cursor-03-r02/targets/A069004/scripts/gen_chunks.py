#!/usr/bin/env python3
"""Split the Epoch Anthropic A069004 Spec.lean into independently compiled chunks."""

from __future__ import annotations

import re
from pathlib import Path

SPEC = Path("/tmp/epoch-a069004/ant/Spec.lean")
OUT = Path("/workspace/research/batches/b01/workers/cursor-03-r02/targets/A069004")

HEADER = """\
/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.
Licensed under the Apache License, Version 2.0.
Original Lean formalization: The Formal Conjectures Authors.
New Lean proof development: Wentao Li.
Certificate data from Epoch Anthropic oeis-full-50usd-ant-j0j0g4uzligm1k41.
-/
import Core

/-! Independent Pratt-certificate chunk {name} from the Epoch Anthropic database. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

"""

COUNT_HEADER = """\
/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.
Licensed under the Apache License, Version 2.0.
Original Lean formalization: The Formal Conjectures Authors.
New Lean proof development: Wentao Li.
Prime-count block data from Epoch Anthropic oeis-full-50usd-ant-j0j0g4uzligm1k41.
-/
import Core

/-! Independent trial-division prime-count block {name}. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

"""


def main() -> None:
    text = SPEC.read_text().splitlines()
    # --- certificate chunks ---
    starts = []
    for i, line in enumerate(text):
        m = re.match(r"def (C\d+) : List", line)
        if m:
            starts.append((m.group(1), i))
    lastS = {}
    last_s_val = {}
    for line in text:
        m = re.match(
            r"theorem hchk(\d+) : Cert\.okChain 512720 (\d+) C\d+ = true", line
        )
        if m:
            lastS[int(m.group(1))] = int(m.group(2))
        m = re.match(r"theorem hfs(\d+) : Cert\.finalS .* = (\d+) :=", line)
        if m:
            last_s_val[int(m.group(1))] = int(m.group(2))

    names = []
    for j, (name, start) in enumerate(starts):
        end = starts[j + 1][1] if j + 1 < len(starts) else None
        if end is None:
            # stop before `def chunks`
            end = next(i for i, l in enumerate(text) if l.startswith("def chunks"))
        body = "\n".join(text[start:end]).rstrip() + "\n"
        idx = int(name[1:])
        ls = lastS[idx]
        fs = last_s_val[idx]
        n_entries = sum(1 for l in text[start:end] if re.match(r"\(\d+, \(PC\.node", l))
        (OUT / f"{name}.lean").write_text(
            HEADER.format(name=name)
            + body
            + "\n"
            + f"theorem hchk{idx} : okChain 512720 {ls} {name} = true := by decide +kernel\n"
            + f"theorem hfs{idx} : finalS {ls} {name} = {fs} := by decide\n"
            + f"theorem hlen{idx} : {name}.length = {n_entries} := by decide\n"
        )
        names.append((name, idx, ls, fs, n_entries))
    print("wrote", len(names), "cert chunks")

    # --- countRange blocks ---
    steps = []
    for line in text:
        m = re.match(
            r"theorem cnt(\d+) : Nat\.count \(fun n => Cert\.trialPrimeB n = true\) (\d+) = (\d+) := Cert\.count_step (\d+) (\d+) (\d+) (\d+) (\d+) (\d+)",
            line,
        )
        if m:
            i, hi, tot, lo, leng, hi2, c, prev, tot2 = m.groups()
            steps.append(
                {
                    "i": int(i),
                    "hi": int(hi),
                    "tot": int(tot),
                    "lo": int(lo),
                    "len": int(leng),
                    "hi2": int(hi2),
                    "c": int(c),
                    "prev": int(prev),
                    "tot2": int(tot2),
                }
            )
    print("count steps", len(steps), "last", steps[-1])
    # group 20 per file
    group = 20
    count_files = []
    for gstart in range(0, len(steps), group):
        chunk = steps[gstart : gstart + group]
        fname = f"Count{gstart:03d}"
        parts = [COUNT_HEADER.format(name=fname)]
        for st in chunk:
            parts.append(
                f"theorem hc{st['i']} : countRange {st['lo']} {st['len']} = {st['c']} := by decide +kernel\n"
            )
        (OUT / f"{fname}.lean").write_text("".join(parts))
        count_files.append(fname)
    print("wrote", len(count_files), "count files")
    (OUT / "chunk_index.txt").write_text(
        "\n".join(
            f"{name} idx={idx} lastS={ls} finalS={fs} n={n}"
            for name, idx, ls, fs, n in names
        )
        + "\n"
    )


if __name__ == "__main__":
    main()
