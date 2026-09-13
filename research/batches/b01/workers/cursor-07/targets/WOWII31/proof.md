# WOWII31 proof

Mathematics: Fan Chung's proof of Erdős–Saks–Sós, Theorem 2.2 (1986).
Original statement formalization: The Formal Conjectures Authors.
Prior exact Lean proof: Kenta Kitamura (KitaKen1), July 2026,
linked from DeepMind PR
[#4658](https://github.com/google-deepmind/formal-conjectures/pull/4658).
This independent implementation and write-up: Wentao Li.
AI assistance: Cursor Grok 4.6, used for Lean API search, lemma
engineering, and compile-error repair. The argument follows Chung.

Classification: `known_mathematics_formalization`. Not new mathematics.
Not a first Lean formalization.

## Statement

For a finite connected simple graph `G` on a nontrivial type,
`2 * rad(G) - 1 ≤ path(G)`, where `path G` is the number of vertices in a
largest induced path.

## Argument

Induction on `|V|`. If `r = rad(G) ≤ 1`, a singleton induced path suffices.

If `r ≥ 2`, take a non-cutvertex `vr`. Let `H = G − vr`.

- If `rad(H) ≥ r`, apply induction in `H` and lift the induced path by
  `Embedding.induce`.
- Otherwise `rad(H) ≤ r − 1`. Let `v0` be a centre of `H`. Every vertex
  other than `vr` is at distance at most `r − 1` from `v0`. A neighbour of
  `vr` therefore gives `dist(v0, vr) ≤ r`. Eccentricity of `v0` is at least
  `r`, so `dist(v0, vr) = r`.

Let `p` be a `v0`–`vr` geodesic, written `v0, v1, …, vr`. Some vertex `w`
satisfies `dist(v2, w) ≥ r`. Then `w ≠ vr` and `dist(v0, w) ∈ {r−2, r−1}`.
Let `P` be a `v0`–`w` geodesic.

No vertex of `P` is adjacent to `vj` for `j ≥ 2`, and `v1, …, vr` do not
lie on `P`. Concatenating the reverse of `p` with `P` gives a walk of
`2r−1` or `2r` vertices. It fails to be induced only if `v1` is adjacent
to a vertex of `P` other than `v0`. That extra edge can exist only when
`P` has length `r−1`, and only to the first vertex of `P` after `v0`.
Deleting `v0` then yields an induced path on `2r−1` vertices.

## Lean

The proof is `WOWII31.conjecture31` in `WOWII31.lean`. It does not use the
sorry theorem `WrittenOnTheWallII.GraphConjecture31.conjecture31`.
The `#print axioms` output is `propext`, `Classical.choice`, `Quot.sound`.

Kitamura’s pinned file proves the same type under
`WrittenOnTheWallII.GraphConjecture31.conjecture31` in
https://github.com/KitaKen1/wowii-graph-conjecture-31-lean/blob/a948e9fc07e11b786aee8dadb1376b4d938454d6/lean/GraphConjecture31.lean
