# cursor-07-r02 handoff

Worker branch: `cursor/b01-cursor-07-r02-05fb`
Coordination seed: `dc6f750f34db0ca579f76bc358082157072f2083`
Source baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
Source SHA-256: `870cd77d2cb8bf98fcbe4bdeee7c52620009af97368fc4358dc595af716046c6`

Kickoff UTC: `2026-09-13T01:23:02Z`
Deadline UTC: `2026-09-13T09:23:02Z`

Do not open a PR. Push only this worker branch.
No continuation timer is active. The goal is stopped after a self-audited exact candidate.
Do not work on WOWII31, WOWII133, or any other target.

## Status: `candidate_proof`

`WOWII101.conjecture101` is a self-audited Lean implementation of Hajnal’s independence-core inequality, matching the frozen type of `WrittenOnTheWallII.GraphConjecture101.conjecture101`. Classification: `known_mathematics_formalization`. Not new mathematics. This worker does **not** claim `independently_verified`.

No exact public Lean proof of this frozen type was found in the checked sources recorded in `targets/WOWII101/literature.md`. That search is not a proof of universal absence.

## Credits

- Mathematics: András Hajnal (1965); Levit–Mandrescu, arXiv:1101.4564, Corollaries 2.3–2.4.
- Original statement formalization: The Formal Conjectures Authors.
- New independent Lean development and write-up: Wentao Li.
- AI assistance: Cursor Grok 4.6 Extra High, worker `cursor-07-r02`.

## Reproduction

```sh
sha256sum FormalConjectures/WrittenOnTheWallII/GraphConjecture101.lean
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-07-r02 --against dc6f750f34db0ca579f76bc358082157072f2083
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-07-r02/targets/WOWII101/WOWII101.lean
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-07-r02/targets/WOWII101/WOWII101_audit.lean
```

Expected axioms: `propext`, `Classical.choice`, `Quot.sound`.

Proof SHA-256: `5018f7ba7f2ec8b63d4334b606d8936db097e635f9c959c3d2877ae9dee8e34a`.
Final commit SHA is recorded after the commit that contains this handoff.

See `STATUS.json` and `targets/WOWII101/{proof,literature,verification}.md`.
