# HANDOFF — cursor-05 / A063880

Incomplete research session. No exact proof or disproof. Do not treat this as a candidate.

## Identity

- worker_id: `cursor-05`
- target: A063880, declarations `OeisA63880.mod_216_of_a` and `OeisA63880.unique_primitive_108`
- actual_branch: `cursor/b01-cursor-05-cb88`
- coordination seed: `238f78bdd5701ae4c97a0d70d4e22e2d45770d7a`
- source baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
- source SHA-256: `b50d00e13735613cbe37bd3a25c19130874e8f036ca2a0e3c1aceb177a33c683`
- original kickoff (UTC): 2026-09-12T23:12Z
- this checkpoint (UTC): 2026-09-13T06:55Z
- final commit SHA: `0ff514519abc3408daec0290d30769466f6bf525`

## Reproduction

```sh
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-05
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-05 --against 238f78bdd5701ae4c97a0d70d4e22e2d45770d7a
sha256sum FormalConjectures/OEIS/63880.lean
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-05/targets/A063880/A063880.lean
python3 research/batches/b01/workers/cursor-05/targets/A063880/experiments/abundancy_enum.py
python3 research/batches/b01/workers/cursor-05/targets/A063880/experiments/case_tree.py
python3 research/batches/b01/workers/cursor-05/targets/A063880/experiments/omega3_ten_seven.py
python3 research/batches/b01/workers/cursor-05/targets/A063880/experiments/omega3_five_triples.py
python3 research/batches/b01/workers/cursor-05/targets/A063880/experiments/omega2_six_five.py
python3 research/batches/b01/workers/cursor-05/targets/A063880/experiments/omega3_six_five.py
```

Do not run a full `lake build`, `lake clean`, or `lake update`.

## Status

- current_status: `partial`
- novelty_status: `no_public_solution_found_in_checked_sources`
- proof_declarations: none completed
- unresolved: both frozen theorems; independent proofs of `powerful_of_isPrimitiveTerm` and `exists_primitive_of_a` if those are used later

## Proved this checkpoint (infrastructure only)

- Leftover `6/5` `{7,43,r}` is glued for every `r ≥ 47`.
- Leftover `6/5` `{7,47,r}` is glued at `v₇ = 3` and `v₇ = 4` for every `r ≥ 53`.
- Leftover `6/5` `{7,q,r}` with `43 ≤ q < r` is glued when `v₇ = 2` and when `r ≥ 223`.
- Previous checkpoint still holds: leftover `6/5` `{7,41,r}` glued for every `r ≥ 43`; leftover `6/5` `{7,37,r}` glued for every `r ≥ 41`; leftover `10/7` closed at ω=3; leftover `10/7` ω=4 last prime `≥ 41` glued; leftover `6/5` closed at ω≤2; `{11,13,p}`, `{11,17,p}`, `{11,19,p}`, `{13,17,p}` glued; `{7,q,r}` glued for `11 ≤ q ≤ 31` and for `71 ≤ q < r`; triples `q ≥ 23` with smallest prime `≥ 11` glued; triples `q ≥ 19` with smallest prime `≥ 13` glued; `{5^2,q,r}` glued for `313 ≤ q < r`; CRT reduction; `v₂≥3 ⇒ v₃<2`.

## Next step

Continue leftover `6/5` ω=3 (`{7,47,r}` at `v₇ ≥ 5` with `r ≤ 211`, then `{7,q,r}` with `53 ≤ q < 71`, `v₇ ≥ 3`, and `r < 223`, then `{5,q,r}` with `q < 313`) and leftover `10/7` ω=4 with last prime `≤ 37` or a factor `5`. Then leftover `100/91` and leftover `2`. CRT plus `v₂ = 2` and `v₃ ≥ 3` already implies the congruence. Do not claim Eldar’s decomposition or the `10^18` search as a new resolution. Do not open a PR.

## Cross-owner notes

No contact with other workers. No discovered equivalence that crosses assignments.
