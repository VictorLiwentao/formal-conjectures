# Verification — WOWII20

Worker: `cursor-07-r04`
Declaration proved: `WOWII20.conjecture20`
Frozen declaration: `WrittenOnTheWallII.GraphConjecture20.conjecture20`
Self-review cannot set `independently_verified`.

## Source pin

```
969908dc9e73fd3ebea73cdf272df476583efbe9745185fd466726c5d4faa2e7  FormalConjectures/WrittenOnTheWallII/GraphConjecture20.lean
```

Lean: `leanprover/lean4:v4.33.1`.
Coordination seed: `7a37b78ee539aab88ebbb77a2579f838e9fcc7a6`.
Working tree edits are confined to `research/batches/b01/workers/cursor-07-r04/`.
The frozen source and `FormalConjecturesForMathlib` were not edited.

## Commands

```sh
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true \
  research/batches/b01/workers/cursor-07-r04/targets/WOWII20/WOWII20.lean
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true \
  research/batches/b01/workers/cursor-07-r04/targets/WOWII20/WOWII20_audit.lean
```

Both succeeded on 2026-09-13T03:23:02Z.

## Axiom log (`WOWII20.conjecture20`)

```
'WOWII20.conjecture20' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Allowed closure. No `sorryAx`, `native_decide`, or `Lean.trustCompiler`.
No `sorry`, `admit`, or `native_decide` in the worker Lean files.

## Exact type

Pretty-print of `WOWII20.conjecture20`:

```
WOWII20.conjecture20.{u_1} {α : Type u_1} [Fintype α] [DecidableEq α] [Nontrivial α]
  (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
  have deg_avg := (∑ v, ↑(G.degree v)) / ↑(Fintype.card α);
  ↑(Fintype.card α) / ↑⌊deg_avg⌋ ≤ G.b
```

Pretty-print of frozen `WrittenOnTheWallII.GraphConjecture20.conjecture20`:

```
WrittenOnTheWallII.GraphConjecture20.conjecture20.{u_1} {α : Type u_1} [Fintype α]
  [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
  (h : G.Connected) :
  have deg_avg := (∑ v, ↑(G.degree v)) / ↑(Fintype.card α);
  ↑(Fintype.card α) / ↑⌊deg_avg⌋ ≤ G.b
```

The statements agree after the namespace prefix. The proof file also contains an
`example` with the frozen `let deg_avg` binders. `b` is the unchanged
ForMathlib real cast of the induced-bipartite `sSup`.

The audit file imports the sorry source only to `#check` / `#print` it. It is
not a proof of the frozen theorem.

## Definition audit

- Induced bipartite: `SimpleGraph.IsBipartite` via
  `induce_isBipartite_iff_exists_coloring`.
- Floor: `Int.floor` of the real average, then cast to real.
- Average: `(∑ v, (G.degree v : ℝ)) / (Fintype.card α : ℝ)`.
- Domain: `[Fintype α] [DecidableEq α] [Nontrivial α]`, `G.Connected`.
- No replacement of floor by ceiling, no weakening of connectedness, no
  admitted source helpers.
