#!/usr/bin/env python3
"""Generate stepwise GlueCert.lean from chunk_index.txt."""

from __future__ import annotations

from pathlib import Path

ROOT = Path("/workspace/research/batches/b01/workers/cursor-03-r02/targets/A069004")
INDEX = ROOT / "chunk_index.txt"

HEADER = """\
/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.
Licensed under the Apache License, Version 2.0.
Original Lean formalization: The Formal Conjectures Authors.
New Lean proof development: Wentao Li.
-/
"""


def main() -> None:
    rows = []
    for line in INDEX.read_text().splitlines():
        if not line.strip():
            continue
        parts = dict(p.split("=", 1) for p in line.split()[1:])
        name = line.split()[0]
        rows.append(
            {
                "name": name,
                "idx": int(parts["idx"]),
                "lastS": int(parts["lastS"]),
                "finalS": int(parts["finalS"]),
                "n": int(parts["n"]),
            }
        )
    n = len(rows)
    names = [r["name"] for r in rows]
    imports = "\n".join(f"import {name}" for name in names)
    chunk_list = ", ".join(names)
    hlen_names = ", ".join(f"hlen{i}" for i in range(n))
    parts = [
        HEADER,
        imports,
        "",
        "/-! Glue independently compiled Pratt chunks into one sorted witness chain. -/",
        "",
        "set_option maxHeartbeats 0",
        "set_option maxRecDepth 1000000",
        "",
        "open Cert",
        "",
        f"def chunks : List (List (ℕ × PC)) := [{chunk_list}]",
        "",
    ]
    # Stepwise from the tail so each proof term is a single `okChunks_cons`.
    for i in range(n - 1, -1, -1):
        rest = ", ".join(names[i:])
        tail = ", ".join(names[i + 1 :])
        lastS = rows[i]["lastS"]
        finalS = rows[i]["finalS"]
        name = names[i]
        if i == n - 1:
            proof = (
                f"okChunks_cons 512720 {lastS} {finalS} {name} [] "
                f"hchk{i} hfs{i} rfl"
            )
        else:
            proof = (
                f"okChunks_cons 512720 {lastS} {finalS} {name} [{tail}] "
                f"hchk{i} hfs{i} hglue{i + 1}"
            )
        parts.append(
            f"theorem hglue{i} : okChunks 512720 {lastS} [{rest}] = true :=\n  {proof}\n"
        )
    parts.append(
        "theorem hchunks : okChunks 512720 0 chunks = true := by\n"
        "  rw [chunks]\n"
        "  exact hglue0\n\n"
        "theorem hflat : okChain 512720 0 chunks.flatten = true :=\n"
        "  okChunks_flatten 512720 chunks 0 hchunks\n\n"
        "theorem hlen : chunks.flatten.length = 42494 := by\n"
        f"  simp [chunks, {hlen_names}]\n"
    )
    (ROOT / "GlueCert.lean").write_text("\n".join(parts))
    print("wrote GlueCert.lean", n, "chunks")


if __name__ == "__main__":
    main()
