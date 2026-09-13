# WOWII31 literature

Classification: `known_mathematics_formalization`. Not new mathematics.

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

## Exact Lean proof search (2026-09-13)

Checked:

- Frozen and live DeepMind `GraphConjecture31.lean` (still `sorry`)
- DeepMind PR #4567 (docs only)
- Mathlib `SimpleGraph` radius/path APIs (`ediam_le_two_mul_radius` is the
  diameter bound, not an induced-path bound)
- GitHub search for a Lean proof of this exact inequality
- No AlphaProof Nexus or Epoch submission with this exact type found

No exact public Lean proof of the frozen type was found. An already existing
exact Lean proof would retire this target.

## Formalization notes

- `path G` is induced-path order, not average distance.
- The frozen type requires `[Nontrivial α]`, `G.Connected`, and compares
  `2 * G.radius.toNat - 1` with `path G` in `ℤ`.
- The worker proof does not import the sorry declaration.
