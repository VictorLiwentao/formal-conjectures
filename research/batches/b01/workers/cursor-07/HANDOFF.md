# cursor-07 handoff

Worker branch: `cursor/b01-cursor-07-ca94`
Baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
Coordination seed: `238f78bdd5701ae4c97a0d70d4e22e2d45770d7a`

Do not open a PR. Push only this worker branch.
Continuation timer `sub_a3edb753-1509-42db-8eac-381a75e58d80` is cancelled.
Do not launch or select another target. Original 8-hour deadline from
`2026-09-12T23:13:00Z` is unchanged.

## Status: `audit_pending`

Coordinator candidate compilation of this branch passed. This worker
does **not** claim `independently_verified`.

Novelty: `prior_solution_found`. Kenta Kitamura (KitaKen1) published an
earlier exact Lean proof of the same frozen type in July 2026. The
coordinator is compiling that prior artifact. That compile is not
confirmed here.

## Credits

- Mathematics: Fan Chung, in Erdős–Saks–Sós Theorem 2.2 (1986).
- Original statement formalization: The Formal Conjectures Authors.
- Prior exact Lean proof: Kenta Kitamura (KitaKen1),
  https://github.com/KitaKen1/wowii-graph-conjecture-31-lean/blob/a948e9fc07e11b786aee8dadb1376b4d938454d6/lean/GraphConjecture31.lean
  linked from https://github.com/google-deepmind/formal-conjectures/pull/4658
- This later independent implementation and write-up: Wentao Li.

## Candidate

`WOWII31.conjecture31` is a later Lean implementation of Chung's proof of
Erdős–Saks–Sós Theorem 2.2. Classification:
`known_mathematics_formalization`. It is not a first formalization.

Proof commit: `a4a7b8cb4557aa7ed7d76947382e48bd18ef40e5`.
Handoff commit previously fetched by the coordinator: `54991f4b`.
Pause checkpoint commit: `629d5307`.

## Reproduction

```sh
sha256sum FormalConjectures/WrittenOnTheWallII/GraphConjecture31.lean
LEAN_NUM_THREADS=2 lake env lean research/batches/b01/workers/cursor-07/targets/WOWII31/WOWII31.lean
LEAN_NUM_THREADS=2 lake env lean research/batches/b01/workers/cursor-07/targets/WOWII31/WOWII31_audit.lean
```

Expected axioms: `propext`, `Classical.choice`, `Quot.sound`.

See `STATUS.json` and `targets/WOWII31/{proof,literature,verification}.md`.

## WOWII133 screening (paused, not selected)

Incomplete screening notes are in `SCREENING.md`. No successor target is
active. Preserve those notes; do not start a WOWII133 proof.
