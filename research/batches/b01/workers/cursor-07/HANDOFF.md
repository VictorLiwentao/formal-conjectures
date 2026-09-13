# cursor-07 handoff

Worker branch: `cursor/b01-cursor-07-ca94`
Baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
Coordination seed: `238f78bdd5701ae4c97a0d70d4e22e2d45770d7a`

Do not open a PR. Push only this worker branch.

## Candidate

`WOWII31.conjecture31` is a Lean formalization of Chung's proof of
Erdős–Saks–Sós Theorem 2.2. Classification:
`known_mathematics_formalization`. Not new mathematics.

## Reproduction

```sh
sha256sum FormalConjectures/WrittenOnTheWallII/GraphConjecture31.lean
LEAN_NUM_THREADS=2 lake env lean research/batches/b01/workers/cursor-07/targets/WOWII31/WOWII31.lean
LEAN_NUM_THREADS=2 lake env lean research/batches/b01/workers/cursor-07/targets/WOWII31/WOWII31_audit.lean
```

Expected axioms: `propext`, `Classical.choice`, `Quot.sound`.

See `STATUS.json` and `targets/WOWII31/{proof,literature,verification}.md`.

## Final commit SHA

Filled after the commit that contains this file's SHA line.
