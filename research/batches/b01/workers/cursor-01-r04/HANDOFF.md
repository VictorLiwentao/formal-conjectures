# HANDOFF — cursor-01-r04

Worker: `cursor-01-r04`
Target: `OeisA1818.conjecture1` (A001818-C1 only)
Actual branch: `cursor/b01-cursor-01-r04-6ddf`
Preferred branch name from the prompt: `codex/b01-cursor-01-r04`
Seed / baseline: `7a37b78ee539aab88ebbb77a2579f838e9fcc7a6`
Source baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
Source SHA-256: `1e41db84e11a5adb981526a75330a597a13ceef8479eb4fb4ef832256496dffe`
Session start UTC: `2026-09-13T02:54:27Z`
Deadline UTC: `2026-09-13T10:54:27Z`
Follow-ups do not restart this clock.

## Reproduction

```bash
export LEAN_NUM_THREADS=2
sha256sum FormalConjectures/OEIS/1818.lean
lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-01-r04/targets/A001818-C1/A001818.lean
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-01-r04 --against 7a37b78ee539aab88ebbb77a2579f838e9fcc7a6
```

Public push: only `origin` `cursor/b01-cursor-01-r04-6ddf` on `https://github.com/VictorLiwentao/formal-conjectures.git`.
No PRs. No other branches. No subagents. No shared-control edits. No C2 / A002454 / A356041 assignment.

## Status

In progress toward an exact C1 candidate. Not independently verified. Not a solution until the frozen statement compiles with allowlisted axioms only.

Proved in worker Lean (allowlisted axioms only): `n=1` case; denominator nonvanishing; Calogero kernel sums and Fourier diagonalization; `det(calogero) = (-1)^n a n`; `per(M-J) = 2^{2n}` times the unsigned derangement sum of `(1-ζ^{σi-i})⁻¹`; signed derangement sum `= (-1)^n a n / 2^{2n}`; Guo 3.1 insertion kernel, rotate-class sum, and the sum over all listings through a fixed point (`sum_cycleEdgeWeight_ncycles`); `cycleEdgeWeight` equals a support-constant times the `(1-ζ)^{-1}` product (`cycleEdgeWeight_zeta`); listings through a fixed point are n-cycles with full support.

Still needed: vanish long-cycle derangement terms, even-size sign cancellation, `per M = per(M-J)`.

## Attribution

Original Lean: The Formal Conjectures Authors.
New Lean development: Wentao Li.
Mathematics: She–Sun–Xia 2022; Guo–Li–Tao–Wei 2022; Calogero–Perelomov 1979.
AI: Cursor Grok 4.6 Extra High, 2026-09-13.
