# HANDOFF — cursor-07-r04 / WOWII20

Worker: `cursor-07-r04`
Target: `WrittenOnTheWallII.GraphConjecture20.conjecture20`
Status: self-audited exact candidate, pending coordinator independent audit.
Independently verified: false.

Branch: `cursor/b01-cursor-07-r04-9d2b`
(Cloud naming required `cursor/…-9d2b`; preferred `codex/b01-cursor-07-r04` was not used.)
Remote: `https://github.com/VictorLiwentao/formal-conjectures.git`
Seed: `7a37b78ee539aab88ebbb77a2579f838e9fcc7a6`
Frozen baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
Source SHA256: `969908dc9e73fd3ebea73cdf272df476583efbe9745185fd466726c5d4faa2e7`
Kickoff UTC: `2026-09-13T02:53:13Z`
Deadline UTC: `2026-09-13T10:53:13Z` (eight hours, never reset)
Worker stopped: `2026-09-13T03:23:02Z`
Candidate commit: `a8f7beecbfa4235fe6bfaa4a64c0b5babb2859d1`
Documentation correction commit: `b7b4b709c20b8d6fdfcbee39123424b6275fc71c`

Proof file: `research/batches/b01/workers/cursor-07-r04/targets/WOWII20/WOWII20.lean`
Audit file: `research/batches/b01/workers/cursor-07-r04/targets/WOWII20/WOWII20_audit.lean`

Mathematics: Alon–Kahn–Seymour 1987, Theorem 1.3 / Corollary 1.4, specialized to induced 2-colorable sets. Not a new mathematical discovery.
Frozen statement: The Formal Conjectures Authors, 2025.
New Lean development and write-up: Wentao Li, 2026.
AI assistance: Cursor Grok 4.6 Extra High.

Reproduce:

```sh
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true \
  research/batches/b01/workers/cursor-07-r04/targets/WOWII20/WOWII20.lean
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true \
  research/batches/b01/workers/cursor-07-r04/targets/WOWII20/WOWII20_audit.lean
```

Expected `#print axioms WOWII20.conjecture20`:
`[propext, Classical.choice, Quot.sound]`

Pretty-printed type of `WOWII20.conjecture20` matches the frozen sorry theorem:
`have deg_avg := (∑ v, ↑(G.degree v)) / ↑(Fintype.card α); ↑(Fintype.card α) / ↑⌊deg_avg⌋ ≤ G.b`

No PR. Push only this worker branch. Coordinator selects replacement or accepts.
