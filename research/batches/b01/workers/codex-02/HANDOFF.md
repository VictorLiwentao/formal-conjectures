# codex-02 handoff

Both targets are retired with status `prior_solution_found`.
The exact conjectures follow from Coster's published Theorem 4 and the cited
cubic ballot identity, through the explicit telescoping calculation in
[literature-reduction.md](literature-reduction.md). This is a source-based
deduction pending independent review, not a new complete Lean proof.

- Worker branch: `codex/b01-codex-02`.
- Source baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
- Coordination seed: `238f78bdd5701ae4c97a0d70d4e22e2d45770d7a`.
- Final commit SHA is reported after commit/push in the task handoff; obtain the
  checked-out branch tip with `git rev-parse HEAD`.
- Only this worker directory is changed. No PR or OEIS edit was made.

## What to review

Read the joint derivation first. The key formula is
`2 Q(N) = 3 S(N) - H(N)^2`, where `Q(N)` is the integer normalized ballot sum,
`S(N) = A112029(N-1)`, and `H(N) = choose(2N-1,N-1)`.
Coster's shifted `(A,B,epsilon)=(0,2,1)` case handles `S`.
Its unshifted `(2,0,1)` case and Vandermonde handle `2H`.
Since the modulus is odd, both targets follow. The raw sequence is `H*Q`.
The cited cubic identity gives an integer formula for `Q` before any numerator
or modular reasoning, so there is no hidden integrality assumption.

The conditional Lean files check the final algebra under explicit inputs;
those inputs have not been formalized here. They do not establish a complete
formal solution. The separate exact-type audit compares their conclusions with
the frozen declarations without using the source proof terms.

The public ballot partial report at commit
`3085b46fdbce945d156d2b5b8b9d1a66627b4375` leaves this case unresolved while
separately citing the applicable Coster square-sum result. No inference about its
other cases is made. The equivalent A183069 record is within this assignment's
mathematical scope. No dependency on another worker's reserved problem was found.
No other agents were contacted or launched.

The live OEIS attribution is Peter Bala (March 2023). The frozen Sun/2019
attribution is a separate documentation correction for the coordinator to review.
OEIS editability and pending drafts remain unknown.

## Reproduce

From the repository root, using Lean `leanprover/lean4:v4.33.1`:

```sh
bash research/batches/b01/workers/codex-02/setup.sh /path/to/compatible/.lake
bash research/batches/b01/workers/codex-02/verify.sh
python3 research/batches/b01/workers/codex-02/experiments.py
```

Skip setup when the private runtime already exists. It copies compatible cached
dependencies to `cache/runtime/.lake`; it does not share a writable cache.
The runtime mirrors the pinned project configuration and uses read-only source
symlinks. Only the two assigned source modules are requested as build targets.
Use a fresh checkout of this worker branch, or the pinned baseline plus the
worker files. Network cache retrieval or toolchain installation is not automated.

`experiments.json` records 499 admissible congruence cases and exact checks of the
normalization identities. This finite computation is not a general proof.
See [verification.md](verification.md) for actual compile results and limits.

## Next action

The coordinator should obtain a fresh independent audit of the mathematical
reduction and exact source mapping, then decide how to retire these entries and
whether a separate formalization task is worthwhile. Do not call either target
independently verified or advertise a new theorem on the basis of this handoff.
