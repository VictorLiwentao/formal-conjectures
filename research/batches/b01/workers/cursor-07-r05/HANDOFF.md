# HANDOFF — cursor-07-r05 / WOWII7

Worker: `cursor-07-r05`
Target: `WrittenOnTheWallII.GraphConjecture7.conjecture7`
Status: self-audited exact candidate, pending coordinator independent audit.
Independently verified: false.

Branch: `cursor/b01-cursor-07-r05-e27b`
(Cloud naming required `cursor/…-e27b`; preferred `codex/b01-cursor-07-r05` was not used.)
Remote: `https://github.com/VictorLiwentao/formal-conjectures.git`
Seed: `027daebfe1c7b664055c00cd4add0dd0419515d1`
Frozen baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
Source SHA256: `b24ee6ea69c547654647cdad7102ce95e64dc8a455fbd9aa12f7214b3d3c3968`
Candidate SHA256: `c85feea04b8babc79e8fd9a5c227f74ed725534edaa101a63f7e4d0ef1e3244c`
Kickoff UTC: `2026-09-13T03:44:44Z`
Deadline UTC: `2026-09-13T11:44:44Z` (eight hours, never reset)
Worker stopped: `2026-09-13T04:05:20Z`
Candidate commit: recorded in the documentation follow-up commit after this file is first committed.

Proof file: `research/batches/b01/workers/cursor-07-r05/targets/WOWII7/WOWII7.lean`
Audit file: `research/batches/b01/workers/cursor-07-r05/targets/WOWII7/WOWII7_audit.lean`

Mathematics: DeLaVina–Fajtlowicz–Waller, *On Some Conjectures of Griggs and Graffiti*, March 2002 / May 2003, Conjecture 2 and Lemma 1. Not a new mathematical discovery.
Frozen statement: The Formal Conjectures Authors, 2026.
New Lean development and write-up: Wentao Li, 2026.
AI assistance: Cursor Grok 4.6 Extra High.
Reused Lean authors: The Formal Conjectures Authors for `Ls` / `indepNeighborsCard` / `indepNum`. Public WOWII2 Lean (Nexus, kingcharlezz, KitaKen) was inspected and not copied.

Reproduce:

```sh
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true \
  research/batches/b01/workers/cursor-07-r05/targets/WOWII7/WOWII7.lean
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true \
  research/batches/b01/workers/cursor-07-r05/targets/WOWII7/WOWII7_audit.lean
```

Expected `#print axioms WOWII7.conjecture7`:
`[propext, Classical.choice, Quot.sound]`

Pretty-printed type of `WOWII7.conjecture7` matches the frozen sorry theorem:
`have maxL := (image (fun v => G.indepNeighborsCard v) univ).max' ⋯; ↑↑maxL - 1 + ↑↑(Fintype.card α) - 2 * ↑↑G.indepNum ≤ G.Ls`

Integer subtraction is on `ℤ` before the real cast. `Ls` is the real supremum over spanning subgraphs whose coercions are trees; leaves have subgraph degree one.

No PR. Push only this worker branch. Coordinator selects replacement or accepts.
Goal and continuation timers are deactivated after this self-audited candidate.
