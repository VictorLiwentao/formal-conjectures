# Proof outline — WOWII20

Mathematics: Alon–Kahn–Seymour 1987, Theorem 1.3 / Corollary 1.4, specialized
to induced 2-colorable sets. Not a new mathematical result.

## Weight lemma

For every finite simple graph, there is an induced bipartite vertex set `s`
with `|s| ≥ ∑_v min(1, 2/(deg(v)+1))`. Proof: induction on `n`.

If some vertex has degree `≤ 1`, delete it. Degrees in the remainder do not
increase, so the weight drops by at most 1. Reinsert the vertex with the
opposite colour of its unique neighbour, if that neighbour was kept.

Otherwise every degree is at least 2. Delete a maximum-degree vertex `v`.
Each of the `D = deg(v)` neighbours gains at least `2/(D(D+1))` in weight,
which offsets the deleted weight `2/(D+1)`.

## Connected nontrivial graphs

Every degree is at least 1, so the weight is `∑ 2/(deg+1)`. Chebyshev /
Cauchy–Schwarz for the antivarying pair `(1/(d+1), d+1)` yields
`∑ 2/(deg+1) ≥ 2n/(d_avg+1)`.

If `d_avg ≥ 2` and `k = ⌊d_avg⌋`, then `d_avg+1 ≤ 2k`, hence
`n/k ≤ 2n/(d_avg+1)`.

If `d_avg < 2`, connectedness gives at least `n-1` edges and the average
gives fewer than `n` edges, so the graph is a tree, hence bipartite, and
`⌊d_avg⌋ = 1`.

`b(G)` is the real cast of the finite `sSup` of induced bipartite sizes.
Any feasible `s` is a witness.
