# Literature and prior Lean audit — WOWII20

Worker: `cursor-07-r04`
Target: `WrittenOnTheWallII.GraphConjecture20.conjecture20`
Classification: known mathematics, formalization only. Not a new mathematical discovery.
Self-review cannot set `independently_verified`.

## Mathematical credit

Primary bound: N. Alon, J. Kahn and P. D. Seymour, Large induced degenerate
subgraphs, Graphs and Combinatorics 3 (1987), 203–211.
DOI: https://doi.org/10.1007/BF01788542
Author PDF: https://web.math.princeton.edu/~nalon/PDFS/Publications/Large%20induced%20degenerate%20subgraphs%20in%20graphs.pdf
Read 2026-09-13. Theorem 1.3 gives an induced `d`-degenerate set of size at
least `∑_v min(1, d/(deg(v)+1))` in their degeneracy convention. Their `d=2`
(forests) is the weight `∑ min(1, 2/(deg(v)+1))`. The induction on p.208
deletes a vertex of degree `< d` and reinserts it, or deletes a maximum-degree
vertex and checks that the weight does not fall. Corollary 1.4 gives size at
least `2n/(d_avg+1)` when `d_avg ≥ 2`.

Independent restatement: N. Alon, D. Mubayi and R. Thomas, Large induced
forests in sparse graphs, introduction.
https://www.cs.tau.ac.il/~nogaa/PDFS/amt4.pdf

Original WOWII portal cited by the frozen file:
http://cms.dt.uh.edu/faculty/delavinae/research/wowII/
The coordinator screen could not independently name a WOWII20 solver. This
worker credits the inequality to AKS 1987 rather than inventing a Graffiti
solver attribution.

Forest/acyclic graphs are 2-colorable. Mathlib already proves
`SimpleGraph.IsAcyclic.isBipartite` and `SimpleGraph.IsTree.isBipartite`.
The formalization produces an induced 2-colorable set of AKS weight directly,
which is sufficient for `b(G)` and matches the frozen bipartite definition.

## Formalization credit

Frozen Lean statement: The Formal Conjectures Authors, 2025, Apache-2.0,
`FormalConjectures/WrittenOnTheWallII/GraphConjecture20.lean` at
`a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
Helpers used without change: `b`, `largestInducedBipartiteSubgraphSize`,
`induce_isBipartite_iff_exists_coloring` in
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Induced.lean`
(no `sorry` in that directory).
New Lean development and write-up: Wentao Li, 2026.
AI assistance: Cursor Grok 4.6 Extra High, disclosed.

## Bounded public Lean search (2026-09-13)

Coordinator screen `replacement-screening-05.md` already searched all-state
DeepMind issues/PRs, Epoch and AlphaProof Nexus clones, and GitHub Lean code
for GraphConjecture20, Alon–Kahn–Seymour, and induced-forest bounds. No
sufficient public proof was compiled there.

This worker rechecked before substantial work and again before the final claim.

Local:

- Mathlib `SimpleGraph` and `FormalConjecturesForMathlib` graph files:
  degeneracy and largest-induced-tree *definitions* exist; no weighted AKS
  bound, no `conjecture20` proof.
- Frozen source remains `sorry` (`@[category research solved]`).
- `FormalConjecturesForMathlib` contains no `sorry`.
- Source SHA256 still
  `969908dc9e73fd3ebea73cdf272df476583efbe9745185fd466726c5d4faa2e7`.

GitHub (authenticated `gh search`, 2026-09-13, after an earlier 429):

- `GraphConjecture20` code hits are statement copies / reviews / bench wrappers,
  not proofs. Upstream
  `google-deepmind/formal-conjectures` still has the sorry theorem.
- Issues and PRs in `google-deepmind/formal-conjectures` matching
  `GraphConjecture20`: none.
- `largestInducedBipartiteSubgraphSize` hits: the ForMathlib definition and a
  copied definition in `txmy/ultra-mathematician` (WOWII40 task sources).
- `AllenGrahamHart/FormalConjectures-Bench` task
  `writtenonthewallii-graphconjecture20-conjecture20`: `Target.lean` is still
  `sorry`; `solve.sh` states that no licence-reviewed solution is bundled;
  `GoldenCheck.lean` is a type wrapper, not a proof.
- `tadamcz/fc-review-results` GraphConjecture20 JSON records: reviews of the
  sorry statement; `trivial_proof.attempted` is false.
- `weiyangzen/awesome_theorems` frontier review of this declaration
  (2026-08-10): proved status not independently closed.
- A later `aksWeight` code search returned HTTP 429; no earlier hit existed in
  the successful searches.
- Unrelated public Lean: EvolvingPrograms/erdos-simonovits-degeneracy and
  openai/ten-proofs `CompactnessAndDegeneracy.lean` treat different theorems.
- Excluded equivalents from this batch: WOWII31, WOWII101, Green66,
  A001481/A256435/Erdos222 gap bounds.
- Web queries for “Alon Kahn Seymour induced degenerate Lean” locate the 1987
  paper and later combinatorial strengthenings, not a Lean proof of this bound.
  Hits for “Alon–Saks–Seymour” are a different conjecture.

Absence in this bounded search is not universal priority certification.
No exact or strictly stronger public Lean proof of the frozen statement was
located, so this worker did not stop for prior coverage.
