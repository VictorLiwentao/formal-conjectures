# WOWII31 verification

## Commands

```sh
sha256sum FormalConjectures/WrittenOnTheWallII/GraphConjecture31.lean
git show a2f4a1bb12a28e04a969da78feefac7d1ce49565:FormalConjectures/WrittenOnTheWallII/GraphConjecture31.lean | sha256sum
LEAN_NUM_THREADS=2 lake env lean research/batches/b01/workers/cursor-07/targets/WOWII31/WOWII31.lean
LEAN_NUM_THREADS=2 lake env lean research/batches/b01/workers/cursor-07/targets/WOWII31/WOWII31_audit.lean
```

## Source hash

Both hashes are
`0c49c9a24c81a764e8bed251442f4e5cbda0ec7b22da2a1fcb04cb3ad02d8092`.

## Proof compile

`lake env lean` on `WOWII31.lean` succeeds with no warnings.

`#print axioms WOWII31.conjecture31`:

```
'WOWII31.conjecture31' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, `Lean.ofReduceBool`, or `Lean.trustCompiler`.

The file contains no `sorry` tactic. It does not import
`WrittenOnTheWallII.GraphConjecture31`.

## Type audit

An `example` in `WOWII31.lean` has the exact frozen type and is proved by
`conjecture31`. The audit file `#check`s
`WrittenOnTheWallII.GraphConjecture31.conjecture31` from the sorry source
and prints the same type (pretty-printed):

```
WrittenOnTheWallII.GraphConjecture31.conjecture31.{u_1} {α : Type u_1}
  [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α)
  [DecidableRel G.Adj] (h : G.Connected) :
  2 * ↑G.radius.toNat - 1 ≤ ↑G.path
```

## Formalization audit

- Quantifiers: finite nontrivial vertex type, connected `G`, decidable adjacency.
- `path G` is largest induced-path order, matching ESS `p(G)` and WOWII's
  path number, not average distance.
- `radius.toNat` is the finite radius of a connected finite graph.
- Boundary: `r ≤ 1` is covered; `r ≥ 2` uses a non-cutvertex.
- The result is Chung's 1986 theorem, not a new theorem.
- Kenta Kitamura (KitaKen1) published an earlier exact Lean proof of this
  type in July 2026 (DeepMind PR #4658). This file is a later
  implementation, not a first formalization.

## Independent review

The coordinator reports that this worker candidate compiled. That is not
`independently_verified`. The coordinator is compiling Kitamura’s prior
artifact; that compile is not confirmed here.
