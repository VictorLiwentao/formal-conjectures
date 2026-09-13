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

Self-audited exact C1 candidate pending coordinator audit. Not independently verified.

Worker `conjecture1_frozen` is the frozen statement. `sunMatrix_eq_frozen` is `rfl`. Integer exponents are `ℤ` subtraction. Original `a` is used. The admitted source theorem is not used as a proof.

Compile (2026-09-13 UTC): `lake env lean -DwarningAsError=true` exit 0.

```
'A001818C1.conjecture1' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.conjecture1_frozen' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Route: Guo 3.1 plus Calogero gives `per(M-J)=a n`. Odd-cycle cancellation plus She–Sun–Xia (3.9) and (4.8) give the Cayley recurrence. Matching involutions satisfy the same two-point recurrence. Induction yields Theorem 1.1. On roots of unity the matching sum is Guo's involution sum, so `per M = a n`.

## Attribution

Original Lean: The Formal Conjectures Authors.
New Lean development: Wentao Li.
Mathematics: She–Sun–Xia 2022; Guo–Li–Tao–Wei 2022; Calogero–Perelomov 1979.
AI: Cursor Grok 4.6 Extra High, 2026-09-13.
