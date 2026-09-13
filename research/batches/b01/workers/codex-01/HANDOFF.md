# codex-01 handoff

**Status: partial. A079727 C1–C4 remain without complete Lean proofs or
counterexamples in this branch.** No novelty or independent-verification
claim is made.

- Worker branch: `codex/b01-codex-01`.
- Authorized public fork: `VictorLiwentao/formal-conjectures`.
- Frozen source baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
- Coordinator seed: `238f78bdd5701ae4c97a0d70d4e22e2d45770d7a`.
- Research content commit: recorded below after the scoped commit.
- Final branch-tip SHA is reported with the completion message. Resolve it
  locally with `git rev-parse codex/b01-codex-01`.

## What can be reused

`targets/A079727/proof.md` describes all proved statements and limitations.
The main unconditional Lean reduction is **C3 implies C2**, checked against
both complete frozen theorem types. C2 is equivalent to the common half sum;
C1 is equivalent to that half sum assuming its endpoint cube congruence.
For C4, uniform complete and half block congruences imply the exact full
finite-set assertion. The carry, block, coprime-product, bilinear,
polynomial-kernel and power-series coefficient lemmas have allowed axiom
closures only.

`targets/A079727/informal-route.md` records detailed routes for all four
conjectures. The C1/C2 route uses a two-digit expansion and finite-field
bilinear identities. C4 uses older prime-level and harmonic results.
C3 has a terminating Clausen comparison and a proposed Jacobi formal-group
argument. The latter's geometric facts and their integral normalization
need careful review. No `sorry` theorem supplies those facts in Lean.

The initial C4 counterexample suspicion was refuted by Lean. The product
notation subtracts one from the entire product. For `{3,13}` the index is
19, and the required divisibility holds. Rejected scratch is explicitly
marked; it must not be presented as a disproof or mismatch.

## Reproduce

From this branch at the repository root, with the frozen dependencies:

```bash
bash research/batches/b01/workers/codex-01/verify.sh
```

This builds only the assigned upstream module and the worker's eight proof
and audit files, using two Lean threads. It then reruns all deterministic
screens and checks the printed axiom sets. Logs, JSONL data, exact-type audit,
source hash and the literature coverage are under `targets/A079727/`.

## Next work

1. Independently review the informal bilinear and Jacobi arguments before
   presenting any full mathematical proof claim.
2. Obtain and inspect the Landweber and Yui LNM chapters. The accessible
   ordinary-prime Coster–van Hamme theorem is insufficient by itself.
3. Formalize the binomial unit-block expansion and the published prime-level
   input without `sorry` dependencies. For C3 also formalize the Jacobi map,
   its reduction/normalization, and the logarithmic coefficient comparison.
4. Continue only within A079727 unless the coordinator changes assignments.

No exact prior solution or cross-owner equivalence was established. Live
upstream and result-repository HEADs were rechecked and unchanged at the
checkpoint. No other workers were contacted, no agents were recruited, and
no PR or OEIS edit was made.
