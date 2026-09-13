# WOWII31 literature

Classification: `known_mathematics_formalization`. Not new mathematics.
Not a first Lean formalization.

## Frozen statement

- File: `FormalConjectures/WrittenOnTheWallII/GraphConjecture31.lean`
- Baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
- SHA-256: `0c49c9a24c81a764e8bed251442f4e5cbda0ec7b22da2a1fcb04cb3ad02d8092`
- Declaration: `WrittenOnTheWallII.GraphConjecture31.conjecture31`

The frozen docstring calls `path G` the floor of the average distance and cites
Chung 1988. That prose does not match `SimpleGraph.path`, which is the largest
induced-path order. DeepMind PR
[#4567](https://github.com/google-deepmind/formal-conjectures/pull/4567)
corrects the docs and source citation and leaves the theorem `sorry`.

## Mathematical source

P. Erdős, M. Saks, V. T. Sós, *Maximum induced trees in graphs*,
J. Combin. Theory Ser. B 41 (1986) 61–79.
PDF: https://www.renyi.hu/~p_erdos/1986-08.pdf

Theorem 2.2: for a connected graph G, the largest induced-path order satisfies
`p(G) ≥ 2 rad(G) − 1`. The published proof is credited to Fan Chung.

The same bound is called the Induced Path Theorem in DeLaVina–Waller,
*Independence, radius and Hamiltonian paths* (MATCH 2007).

WOWII lists Conjecture 31 as Chung's theorem:
http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj31

## Prior exact Lean proof (July 2026)

An earlier exact Lean formalization of the same inequality was written by
Kenta Kitamura (KitaKen1) and linked from open DeepMind PR
[#4658](https://github.com/google-deepmind/formal-conjectures/pull/4658)
(opened 2026-07-28). The PR adds a `formal_proof using lean4` pointer; it is
not merged at the frozen baseline.

Pinned Lean file:

https://github.com/KitaKen1/wowii-graph-conjecture-31-lean/blob/a948e9fc07e11b786aee8dadb1376b4d938454d6/lean/GraphConjecture31.lean

Repo: https://github.com/KitaKen1/wowii-graph-conjecture-31-lean

The pinned file proves
`WrittenOnTheWallII.GraphConjecture31.conjecture31` with the same type as
the frozen sorry theorem:

```
{α : Type u} [Fintype α] [DecidableEq α] [Nontrivial α]
(G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)
```

It inlines local `isInducedPath` / `path` copies matching the Formal
Conjectures definitions and proves a natural-number form
`chung_bound_nat` first. The worker’s 2026-09-13 literature pass missed
this PR. That miss is corrected here. This worker file is a later
independent implementation, not the first exact Lean proof.

William J. Blair commented on PR #4658 on 2026-08-08 that the linked
file compiled on Formal Conjectures’ toolchain with no `sorry`. The
coordinator auditor is compiling that prior artifact again. This
worker does not treat that compile as confirmed.

## Other Lean search notes (2026-09-13)

Checked and still accurate after the correction:

- Frozen and live DeepMind `GraphConjecture31.lean` (still `sorry` at freeze)
- DeepMind PR #4567 (docs only)
- Mathlib `SimpleGraph` radius/path APIs (`ediam_le_two_mul_radius` is the
  diameter bound, not an induced-path bound)

No AlphaProof Nexus or Epoch submission with this exact type was found.
Those negative checks do not make the worker file first.

## Formalization notes

- `path G` is induced-path order, not average distance.
- The frozen type requires `[Nontrivial α]`, `G.Connected`, and compares
  `2 * G.radius.toNat - 1` with `path G` in `ℤ`.
- The worker proof does not import the sorry declaration and does not
  import Kitamura’s file.
