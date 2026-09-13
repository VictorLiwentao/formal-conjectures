# Proof of WOWII7 / GraphConjecture7

Mathematics: Ermelinda DeLaVina, Siemion Fajtlowicz and Bill Waller,
*On Some Conjectures of Griggs and Graffiti*, March 2002, revised May 2003,
Conjecture 2 and Lemma 1. This is not a new mathematical discovery.

Frozen statement: The Formal Conjectures Authors, 2026.
New Lean development and write-up: Wentao Li, 2026.
AI assistance: Cursor Grok 4.6 Extra High.

## Target

For a finite connected simple graph `G` on at least two vertices,

\[
L_s(G)\ge n+\mu-2\alpha-1,
\]

where \(\alpha=G.\mathrm{indepNum}\) and \(\mu=\max_v\mathrm{indepNeighborsCard}\,G\,v\).
The Lean form uses integer subtraction before the real cast:

```lean
((maxL : ℤ) - 1 + (Fintype.card α : ℤ) - 2 * (G.indepNum : ℤ) : ℝ) ≤ Ls G
```

`Ls` is the real supremum of the number of degree-one vertices over spanning
subgraphs whose coercions are trees.

## Chain

Connectedness and nontriviality give `1 ≤ indepNeighborsCard G v` for every `v`,
so \(\mu\ge 1\). A maximum independent set `S` in `N(c)` for a vertex `c`
realising \(\mu\) is independent in `G` and does not contain `c`. The seed
`T=S\cup\{c\}` induces a star, hence a connected subgraph, and satisfies
`|T|+\mu\le 2|S|+1`.

A feasible pair `(M,T)` is an independent set `M\subseteq T` such that `G[T]` is
connected, `T` lies in the closed neighbourhood of `M`, and
`|T|+\mu\le 2|M|+1`. Among feasible pairs, take one maximising `|M|`.

If the closed neighbourhood of `M` is not all of `V(G)`, connectedness supplies
a boundary dart `uv` with `u` adjacent to `M` and `v` outside that closed
neighbourhood. Inserting `v` into `M` and `{u,v}` into `T` preserves
feasibility and increases `|M|`, a contradiction. Thus `M` dominates, so `T`
is a connected dominating set, and `|M|\le\alpha` yields
`|T|+\mu\le 2\alpha+1`.

From such a trunk, choose a neighbour in the trunk for every external vertex
and add those pendant edges to the spanning-coe of the trunk. The resulting
graph is connected. Any spanning tree of it has degree one at every external
vertex, because those vertices already have degree one before passing to a
spanning tree, and a nontrivial tree vertex has positive degree. Hence there
are at least `n-|T|` leaves.

Integer arithmetic then gives
`n+\mu-2\alpha-1\le n-|T|`. The constructed spanning subgraph is spanning and
a tree after transport along `Equiv.Set.univ`, so its leaf count is a member
of the `Ls` set. The set is bounded above by `n`, so the real supremum is at
least that count.

## Corners

- `n=2`: the unique spanning tree is an edge; both vertices have degree one.
  The lower expression is at most `0` when \(\mu=1\) and \(\alpha=1\).
- Complete graphs: \(\mu=1=\alpha\), bound `n-2`. A star spanning tree has
  `n-1` leaves for `n\ge 3`. The construction uses a two-vertex trunk and
  claims only `n-|T|` leaves, which is enough.
- The complement of a connected dominating set need not be exactly the leaf
  set. The proof uses only the safe lower bound `n-|T|`.
- The weaker Griggs bound `Ls\ge n-2\alpha+1` is the case \(\mu=2\) of this
  inequality and does not cover \(\mu>2\).
