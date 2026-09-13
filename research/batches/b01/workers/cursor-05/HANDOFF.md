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
- this checkpoint (UTC): 2026-09-13T01:57Z
- final commit SHA: `pending-after-commit`

## Reproduction

```sh
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-05
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-05 --against 238f78bdd5701ae4c97a0d70d4e22e2d45770d7a
sha256sum FormalConjectures/OEIS/63880.lean
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-05/targets/A063880/A063880.lean
python3 research/batches/b01/workers/cursor-05/targets/A063880/experiments/abundancy_enum.py
python3 research/batches/b01/workers/cursor-05/targets/A063880/experiments/case_tree.py
python3 research/batches/b01/workers/cursor-05/targets/A063880/experiments/omega3_ten_seven.py
```

Do not run a full `lake build`, `lake clean`, or `lake update`.

## Status

- current_status: `partial`
- novelty_status: `no_public_solution_found_in_checked_sources`
- proof_declarations: none completed
- unresolved: both frozen theorems; independent proofs of `powerful_of_isPrimitiveTerm` and `exists_primitive_of_a` if those are used later

## Proved this checkpoint (infrastructure only)

- `ρ(p^a)` is strictly increasing in the exponent for `a ≥ 1`.
- Leftover `10/7` cannot be two squareful primes `p < q` both at least `5` times a squarefree factor. This includes the `{5,7}` pair.
- Three squareful primes all at least `7` cannot fill leftover `10/7` (cap `1001/720 < 10/7`).
- Leftover `10/7` ω=3 with a factor `5`: `{5^2,7^2,p^k}` for `p ≥ 23`; Euler caps `{5,11,p≥29}`, `{5,13,p≥23}`, `{5,17,p≥19}`; squares `{5,7,11/13/17/19}` overshoot and lift to all exponents `≥ 2`.
- `{5,11,13}`, `{5,11,17}`, and `{5,11,19}` cannot fill leftover `10/7`. `{5^2,11^b,q^c}` undershoots for every `q≥13`.
- `{5^3,7^2,p^k}` and `{5^2,7^3,p^k}` with `k≥2` cannot fill leftover `10/7` for primes `p≥23`, including the `{5^3,7^2,83^k}` boundary.
- An extra positive factor cannot repair an overshoot. Kernels containing `5^a 7^b 11^c` with `a,b,c≥2` overshoot, including ω≥4 supersets of `{5,7,11}`.
- A `Fraction` search for three primes `≥ 5` on leftover `10/7` returned no hits. That search is not a proof.

## Next step

Continue the local-valuation case analysis in Lean. CRT plus `v₂ = 2` and `v₃ ≥ 3` already implies the congruence (`mod_216_of_A_of_valuations`). Remaining: leftover `10/7` ω=3 `{5,11,23}` and `{5,13,17/19}`; mixed `{5^a,7^b,p}` with a raised exponent beyond the `a=3,b=2` and `a=2,b=3` rays; ω≥4 not containing `{5,7,11}`; leftover `100/91` with primes `≥ 127`; leftover `2`; leftovers `≤ 6/5` without `9`. Do not claim Eldar’s decomposition or the `10^18` search as a new resolution. Do not open a PR.

## Cross-owner notes

No contact with other workers. No discovered equivalence that crosses assignments.
