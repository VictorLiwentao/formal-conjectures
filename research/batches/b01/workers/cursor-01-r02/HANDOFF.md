# HANDOFF — cursor-01-r02

Worker: `cursor-01-r02`
Target: `OeisA109074.conjecture`
Actual branch: `cursor/b01-cursor-01-r02-0918`
Preferred branch name from the prompt: `codex/b01-cursor-01-r02`
Baseline: `1107856a264a066e316c3cba7b5339be475f6304`
Source baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
Source SHA-256: `cd5a2af1993d52ae29df9480d9304cbecae195e24d2ab51a45919806899cfd1e`
Session start UTC: `2026-09-13T00:14:43Z`
Deadline UTC: `2026-09-13T08:14:43Z`
Follow-ups do not restart this clock.

## Reproduction

```bash
export LEAN_NUM_THREADS=2
lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-01-r02/targets/A109074/A109074.lean
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-01-r02 --against 1107856a264a066e316c3cba7b5339be475f6304
```

Public push: only `origin` `cursor/b01-cursor-01-r02-0918` on `https://github.com/VictorLiwentao/formal-conjectures.git`.
No PRs. No other branches. No subagents.

Final commit SHA: `52a9147f45c75e889450d31e3be44497c1b43b48`.

## Status

`candidate_proof`.
Novelty: `known_mathematics_formalization_candidate`.
No exact public completed Lean proof of the frozen statement was located in the bounded repeat audit.

`A109074Proof.conjecture` compiles with axioms `{propext, Classical.choice, Quot.sound}`.
Natural-division integrality (`den_dvd_num`) and positivity (`b_pos`) are proved before rational cancellation.
Self-review cannot set `independently_verified`.

## Proved in `targets/A109074/A109074.lean`

- Algebraic identity `frac_succ`
- Factorization reduction of `den_dvd_num` to `digitSum_ineq`
- 2-adic digit-sum inequality
- Odd-prime digit-sum inequality via floor increments on odd moduli \(Q=p^i\)
- `b_pos`, `b_cast_div`, `b_succ_ratio`, exact-type `conjecture`

Do not replace `b` by a rational sequence. Do not start A237271 or any other assignment.

## Attribution

Original Lean: The Formal Conjectures Authors.
New Lean development: Wentao Li.
Mathematics: Robbins; Kuperberg; Razumov–Stroganov.
AI: Cursor Grok 4.6 Extra High, 2026-09-13.
