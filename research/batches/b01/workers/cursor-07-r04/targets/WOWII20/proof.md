# Proof — WOWII20

Mathematics: N. Alon, J. Kahn and P. D. Seymour, Large induced degenerate
subgraphs, Graphs and Combinatorics 3 (1987), Theorem 1.3 and Corollary 1.4,
specialized to induced 2-colorable vertex sets. Not a new mathematical result.

Frozen statement: for a finite nontrivial vertex type and a connected simple
graph `G`, with `deg_avg = (∑_v deg(v))/n` a real average,

\[
\frac{n}{\lfloor\mathrm{deg\_avg}\rfloor} \le b(G),
\]

where `b(G)` is the real cast of the supremum of cardinalities of vertex sets
that induce a bipartite subgraph. The definition of bipartite is the existing
`IsBipartite` / 2-coloring API. Connectedness and `Nontrivial` are kept.

## Weight lemma

For every finite simple graph there is an induced bipartite set `s` with

\[
|s| \ge \sum_v \min\bigl(1,\ 2/(\deg(v)+1)\bigr).
\]

Proof: induction on `n = |V|`.

If some vertex `v` has degree at most 1, delete it. Every remaining degree is
at most the original degree, so each remaining weight is at least as large.
The deleted weight is at most 1. Reinsert `v` into the inductive set, coloring
it with the opposite colour of its unique neighbour when that neighbour was
kept, or with colour 0 if it has no neighbour in the set.

If every degree is at least 2, delete a maximum-degree vertex `v` of degree
`D`. A neighbour `u` of degree `t` has weight gain `2/(t(t+1))` after the
edge to `v` disappears. Since `2 ≤ t ≤ D`, each gain is at least `2/(D(D+1))`.
There are `D` neighbours, so the total gain is at least the deleted weight
`2/(D+1)`. Non-neighbours keep their weight. The inductive induced set in
`G - v` remains induced bipartite in `G`.

## Connected nontrivial graphs

Every degree is at least 1, so the min-clip disappears and the weight is
`∑ 2/(deg(v)+1)`. Chebyshev for the antivarying pair `(1/(d+1), d+1)` gives

\[
\sum_v \frac{2}{\deg(v)+1} \ge \frac{2n}{\mathrm{deg\_avg}+1}.
\]

If `deg_avg ≥ 2` and `k = ⌊deg_avg⌋`, then `k ≥ 2` and
`deg_avg < k+1`, so `deg_avg + 1 < k+2 ≤ 2k`. Hence
`n/k ≤ 2n/(deg_avg+1)`.

If `deg_avg < 2`, connectedness gives at least `n-1` edges, while the average
gives strictly fewer than `n` edges. Therefore the graph is a tree, hence
bipartite, `b(G) = n`, and `⌊deg_avg⌋ = 1` because also `deg_avg ≥ 1`.

Any feasible vertex set is a witness for the defining `sSup` of `b`. The
supremum is bounded by `n`.

The formalization produces a 2-colorable induced set of AKS weight directly.
It does not need a separate forest-to-bipartite bridge on the inductive set.
The tree corner uses Mathlib `IsTree.isBipartite`.
