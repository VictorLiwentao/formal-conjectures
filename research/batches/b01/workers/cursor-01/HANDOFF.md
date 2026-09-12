# HANDOFF: cursor-01 / A237271

Worker branch: `cursor/b01-cursor-01-8a28`
Coordination seed: `238f78bdd5701ae4c97a0d70d4e22e2d45770d7a`
Frozen source: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
Status: `candidate_proof` of `OeisA237271.observation_carmichael`
No PR opened, as instructed.

## What is proved

`OeisA237271.Cursor01.observation_carmichael` has the frozen type
`∀ k, IsCarmichael k → 3 ≤ a k`. It is deduced from
`a_ge_three_of_odd_composite`: every odd composite has at least two
ordered-divisor jumps counted by `a`. Carmichael numbers are odd
composites by `FermatPsp` at base 1 and the coprime base `k-1`.

Axioms: `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.

## What is not claimed

This is not `independently_verified`. Issue #5447 already had the
informal argument; no public kernel-checked proof of the corrected
declaration was found. Conjecture 2 and the old vacuous hypothesis are
different targets and were not used.

## Reproduce

```sh
git checkout cursor/b01-cursor-01-8a28
export LEAN_NUM_THREADS=2
lake --wfail build 'FormalConjectures.OEIS.«237271»'
lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-01/targets/A237271/A237271.lean
lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-01/targets/A237271/type_audit.lean
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-01 --against 238f78bdd5701ae4c97a0d70d4e22e2d45770d7a
```

Final proof commit: `5c6472e6ebc61681a8b0df5b2066caddc82b0b6e`.
This HANDOFF file may sit one commit later on the same branch.
