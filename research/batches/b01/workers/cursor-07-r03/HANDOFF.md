# cursor-07-r03 handoff

Worker branch: `cursor/b01-cursor-07-r03-ceef`
Coordination seed: `486f35dcee50c2c32b98f946726adbd20f6a5fbf`
Source baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
Source SHA-256: `d38ab7e233260302ef58121037a02dc94866ddae820e9fc84308ce7264e07acb`

Kickoff UTC: `2026-09-13T02:07:46Z`
Deadline UTC: `2026-09-13T10:07:46Z`

Do not open a PR. Push only this worker branch.
No continuation timer is active. The goal is stopped after a self-audited exact candidate.
Do not work on the open Green66 `1/10` statement, WOWII31, WOWII101, or any other target.

## Status: `candidate_proof`

`Green66TrivialBound.trivial_bound` is a self-audited Lean implementation of the known uniform-C `O(X^{1/4})` successive-square bound, matching the frozen type of `Green66.green_66.variants.trivial_bound`. Classification: `known_mathematics_formalization`. Not new mathematics. This does **not** settle Green's open problem 66. This worker does **not** claim `independently_verified`.

No exact public Lean proof of this frozen type was found in the checked sources recorded in `targets/Green66-trivial-bound/literature.md`. That search is not a proof of universal absence.

## Credits

- Mathematics: classical successive greatest-square remainder bound, as described by Ben Green, A list of open problems, problem 66. Bambah–Chowla (1947) is the sharper gap theorem and is not used. Green is an exposition source, not claimed as the discoverer.
- Original statement formalization: The Formal Conjectures Authors.
- New independent Lean development and write-up: Wentao Li.
- AI assistance: Cursor Grok 4.6 Extra High, worker `cursor-07-r03`.
- Related inspected Lean that does not prove this target: LeanGenius `bambah_chowla_upper_bound` axiom; Epoch `oeis_275409` lemma `bambah_chowla` (weaker `O(√X)` forward bound).

## Reproduction

```sh
sha256sum FormalConjectures/GreensOpenProblems/66.lean
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-07-r03 --against 486f35dcee50c2c32b98f946726adbd20f6a5fbf
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-07-r03/targets/Green66-trivial-bound/Green66.lean
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-07-r03/targets/Green66-trivial-bound/Green66_audit.lean
```

Expected axioms: `propext`, `Classical.choice`, `Quot.sound`.

Proof SHA-256: `20e98a7695ed2327099ed3f3d46d6394aea552aa02354287eacf65d0bfb13929`.

See `STATUS.json` and `targets/Green66-trivial-bound/{proof,literature,verification}.md`.
