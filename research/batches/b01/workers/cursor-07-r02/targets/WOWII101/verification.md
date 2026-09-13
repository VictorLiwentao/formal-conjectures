# WOWII101 verification

Self-audit of an exact candidate. Coordinator review remains pending. This worker does not claim `independently_verified`.

## Commands

```sh
sha256sum FormalConjectures/WrittenOnTheWallII/GraphConjecture101.lean
# expected: 870cd77d2cb8bf98fcbe4bdeee7c52620009af97368fc4358dc595af716046c6

python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-07-r02 --against dc6f750f34db0ca579f76bc358082157072f2083

export LEAN_NUM_THREADS=2
lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-07-r02/targets/WOWII101/WOWII101.lean
lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-07-r02/targets/WOWII101/WOWII101_audit.lean
```

No `lake build` of the whole project, no `lake clean`, and no `lake update`. Cached `.lake` oleans were reused.

## Results (2026-09-13T01:41Z)

Proof compile exit code 0 with `-DwarningAsError=true`. Log: `logs/compile-success.log`.

```
'WOWII101.conjecture101' depends on axioms: [propext, Classical.choice, Quot.sound]
WrittenOnTheWallII.GraphConjecture101.conjecture101.{u_1} {α : Type u_1} [Fintype α] [DecidableEq α] [Nontrivial α]
  (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
  α(G) ≤ (Fintype.card α + #(WrittenOnTheWallII.GraphConjecture101.alphaCore G)) / 2
WOWII101.conjecture101.{u_1} {α : Type u_1} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α)
  [DecidableRel G.Adj] (_h : G.Connected) :
  α(G) ≤ (Fintype.card α + #(WrittenOnTheWallII.GraphConjecture101.alphaCore G)) / 2
```

Allowed axioms only. No `sorryAx`, `native_decide`, or `Lean.trustCompiler`. The binder name `_h` versus `h` is pretty-printing; the compiled example applies `WOWII101.conjecture101` at the frozen type.

Audit compile exit code 0. Log: `logs/audit.log`. The frozen declaration still ends in `sorry`. This candidate does not apply that theorem.

Proof SHA-256: `5018f7ba7f2ec8b63d4334b606d8936db097e635f9c959c3d2877ae9dee8e34a`.

## Formalization audit

- Quantifiers, `Fintype`/`DecidableEq`/`Nontrivial`, `DecidableRel G.Adj`, and `G.Connected` match the source.
- `alphaCore` and `indepNumDeleteVertex` are the source definitions.
- `indepNum` is Mathlib’s `sSup` of `IsNIndepSet` sizes. Floor division is `Nat` division.
- `alphaCore` is proved equal to the intersection of all maximum independent sets, which is Hajnal/Levit–Mandrescu `core(G)`.
- Connectedness is unused; the proved bound holds for every finite graph of the frozen type.
- Imports `FormalConjectures.WrittenOnTheWallII.GraphConjecture101` for definitions only. The admitted source theorem is not applied. `#print axioms` has no `sorryAx`.

## Credits

Copyright 2026 The Formal Conjectures Authors. Copyright 2026 Wentao Li.
Original Lean formalization: The Formal Conjectures Authors.
New independent Lean development/write-up: Wentao Li.
Mathematics: Hajnal (1965); Levit–Mandrescu arXiv:1101.4564.
AI assistance: Cursor Grok 4.6 Extra High, worker `cursor-07-r02`.
