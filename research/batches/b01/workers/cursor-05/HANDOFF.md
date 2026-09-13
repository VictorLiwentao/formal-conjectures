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
- this checkpoint (UTC): 2026-09-13T02:53Z
- final commit SHA: `baf2eacc632a7576b5c813db091aff24ef094679`

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
```

Do not run a full `lake build`, `lake clean`, or `lake update`.

## Status

- current_status: `partial`
- novelty_status: `no_public_solution_found_in_checked_sources`
- proof_declarations: none completed
- unresolved: both frozen theorems; independent proofs of `powerful_of_isPrimitiveTerm` and `exists_primitive_of_a` if those are used later

## Proved this checkpoint (infrastructure only)

- Leftover `6/5` is impossible on a squarefree argument.
- Leftover `6/5` cannot be two squareful primes `p < q` both at least `5` times a squarefree coprime factor (`not_five_sigma_of_two_sq_primes`).
- `{5^a, q^k}` with `q ≥ 7` and `a,k ≥ 2` cannot fill leftover `6/5`.
- `{7^a, q^k}` with `q ≥ 11` and `a,k ≥ 2` cannot fill leftover `6/5`.
- If `8m` is in `A` with `m` odd, the same two-prime obstruction applies (`not_A_of_eight_mul_two_sq_primes`).
- Combined with the unique-squareful-prime lemma, leftover `6/5` is closed at ω≤2.
- Previous checkpoint still holds: CRT reduction; leftover `10/7` ω=1 for `p≥5`; ω=2 with two squareful primes `≥5`; ω=3 with all primes `≥7`; leftover `10/7` ω=3-with-5 family-complete including `{5^a,7^b,p}` for `p≥11`; `v₂≥3 ⇒ v₃<2`.

## Next step

Glue the leftover `10/7` ω=3-with-`5` family lemmas onto an arbitrary `n` with three squareful primes. Then leftover `6/5` ω≥3, leftover `100/91`, leftover `2`. CRT plus `v₂ = 2` and `v₃ ≥ 3` already implies the congruence. Do not claim Eldar’s decomposition or the `10^18` search as a new resolution. Do not open a PR.

## Cross-owner notes

No contact with other workers. No discovered equivalence that crosses assignments.
