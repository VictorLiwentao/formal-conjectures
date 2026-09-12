# HANDOFF — cursor-03 / A076141

## Status

`prior_solution_found`. The exact frozen theorem `OeisA76141.conjecture` (`∀ n, a n ≤ 1`) already has a public Lean proof. This worker kernel-checked that file on the batch tree and stopped without reproducing it.

## Branch

- `cursor/b01-cursor-03-91b3`
- Coordination seed: `238f78bdd5701ae4c97a0d70d4e22e2d45770d7a`
- Public prior proof: https://github.com/KitaKen1/oeis-a076141-binary-word/blob/b4e179767fa3041c43e019b559ee77e6737317aa/lean/OeisA76141FC.lean
- Upstream marker PR (open, unreviewed): https://github.com/google-deepmind/formal-conjectures/pull/5088

Final commit SHA: `91ee3819157eb806a97195c135181f0b61a2f3e1` (this handoff file may sit on a later follow-up commit on the same branch). Reproduction:

```sh
git checkout cursor/b01-cursor-03-91b3
git rev-parse HEAD
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-03
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-03 --against 238f78bdd5701ae4c97a0d70d4e22e2d45770d7a
sha256sum FormalConjectures/OEIS/76141.lean
LEAN_NUM_THREADS=2 lake env lean research/batches/b01/workers/cursor-03/targets/A076141/A076141.lean
curl -fsSL -o /tmp/OeisA76141FC.lean https://raw.githubusercontent.com/KitaKen1/oeis-a076141-binary-word/b4e179767fa3041c43e019b559ee77e6737317aa/lean/OeisA76141FC.lean
LEAN_NUM_THREADS=2 lake env lean /tmp/OeisA76141FC.lean
python3 research/batches/b01/workers/cursor-03/targets/A076141/experiments/count_occurrences.py
```

Expected: assignment PASS; source SHA `7954f35f38ed7da506eefc949c1d401e99625a70406561413198c467e63d4c78`; type audit prints `∀ (n : ℕ), OeisA76141.a n ≤ 1` with upstream `sorryAx`; prior file prints axioms `propext`, `Classical.choice`, `Quot.sound`.

## Cross-owner / upstream notes

- No assignment overlap found. A018826 / A136510 are related but not other workers’ reserved groups.
- Do not treat Epoch failures as openness.
- Independent review of the KitaKen1 proof is still required before a public solved claim.

## Session

Original kickoff about 2026-09-12T23:11Z. Stopped after the prior-solution gate, well under the eight-hour budget. No continuation timers. No PRs.
