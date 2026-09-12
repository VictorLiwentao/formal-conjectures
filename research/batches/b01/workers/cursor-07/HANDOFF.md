# cursor-07 handoff

Worker branch: `cursor/b01-cursor-07-ca94`
Baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
Coordination seed: `238f78bdd5701ae4c97a0d70d4e22e2d45770d7a`

## Reproduction

```sh
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-07
sha256sum FormalConjectures/WrittenOnTheWallII/GraphConjecture{19,40,61,100,133,198a,314}.lean
/home/ubuntu/.venvs/fc-research/bin/python3 -u research/batches/b01/workers/cursor-07/scratch/wow_search.py "19,16,40,61,100,133,198a" named
```

Do not open a PR. Push only this worker branch.

## Status

No exact novel proof or disproof yet. See `STATUS.json`, `QUEUE.json`, `SCREENING.md`.

Final commit SHA will be filled after the next commit.
