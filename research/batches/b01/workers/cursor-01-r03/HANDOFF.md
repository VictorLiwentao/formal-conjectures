# HANDOFF — cursor-01-r03

Worker: `cursor-01-r03`
Target: `OeisA51903.conjecture2` (A051903-C2 only)
Actual branch: `cursor/b01-cursor-01-r03-2609`
Preferred branch name from the prompt: `codex/b01-cursor-01-r03`
Seed / baseline: `1ee796fa5606a0027266111e53f9b6c5d11d62a6`
Source baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
Source SHA-256: `3a694eccc4bd92c14e28e609563bad0ecdfb8895f45c6de887b46fcfcd483db4`
Session start UTC: `2026-09-13T02:22:16Z`
Deadline UTC: `2026-09-13T10:22:16Z`
Follow-ups do not restart this clock.

## Reproduction

```bash
export LEAN_NUM_THREADS=2
lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-01-r03/targets/A051903-C2/A051903.lean
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-01-r03 --against 1ee796fa5606a0027266111e53f9b6c5d11d62a6
sha256sum FormalConjectures/OEIS/51903.lean
```

Public push: only `origin` `cursor/b01-cursor-01-r03-2609` on `https://github.com/VictorLiwentao/formal-conjectures.git`.
No PRs. No other branches. No subagents. No shared-control edits.

Candidate commit SHA: `c6ba241ffa46fd146e47d7e33d8e38b6428c104b`.

## Status

Worker self-review: `candidate_proof` only.
Coordinator independent verification: **pending**.
Novelty: `known_mathematics_formalization`. No earlier exact public Lean proof of C2 was found in the checked sources. This is not a new-mathematics claim.

`A051903C2.no_odd_universal` and `A051903C2.conjecture2` compile with axioms `{propext, Classical.choice, Quot.sound}`.
The wrapper is `False ↔` the frozen RHS existential, via `answer(False)`.

Stop after this self-audited candidate. Cancel timers/goal so the slot cannot resume competing work. Do not start C1, C3, A327295 proof work, or any other assignment.

## Proved in `targets/A051903-C2/A051903.lean`

- Maximum exponent attained at an odd prime from the original `primeFactorsList`/`count`/`foldr max` definition
- `n > a n` and `p^(a n) ∣ n`
- Reduction of the all-`b` congruence at `b = 1+p` modulo `p^e`
- Order of `1+p` modulo `p^e` equals `p^(e-1)`
- `p^(e-1) ∣ a n` contradicts `a n < p^(e-1)`
- Explicit `answer(False)` wrapper

## Attribution

Original Lean: The Formal Conjectures Authors.
New Lean development: Wentao Li.
Mathematical question: Thomas Ordowski.
Related prior mathematics: Dutta–Dutta, viXra:2602.0018 (classification; not used as a Lean dependency).
AI: Cursor Grok 4.6 Extra High, 2026-09-13.
