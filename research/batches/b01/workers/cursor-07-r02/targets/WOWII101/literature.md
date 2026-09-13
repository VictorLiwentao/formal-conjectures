# WOWII101 literature

Classification: known mathematics. The acceptable result is a Lean formalization of a known theorem, not a new mathematical discovery. This file records the public exact-Lean search. A source `sorry` or `research solved` label is not a substitute for that search.

## Frozen statement

- File: `FormalConjectures/WrittenOnTheWallII/GraphConjecture101.lean`
- Baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
- Working-tree SHA-256: `870cd77d2cb8bf98fcbe4bdeee7c52620009af97368fc4358dc595af716046c6` (matches the assignment pin)
- Live `main` retrieved 2026-09-13: same SHA-256, still `sorry`
- Declaration: `WrittenOnTheWallII.GraphConjecture101.conjecture101`
- Source URL: https://github.com/google-deepmind/formal-conjectures/blob/a2f4a1bb12a28e04a969da78feefac7d1ce49565/FormalConjectures/WrittenOnTheWallII/GraphConjecture101.lean
- Original statement PR: https://github.com/google-deepmind/formal-conjectures/pull/3820 (merged 2026-06-08)

Type (quantifiers in source order):

```
∀ {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected),
  G.indepNum ≤ (Fintype.card α + (alphaCore G).card) / 2
```

`alphaCore G` is the Finset of vertices `v` with `indepNumDeleteVertex G v < G.indepNum`, and `indepNumDeleteVertex G v` is `(G.induce (Set.univ \ {v})).indepNum`. Natural division is floor division: the inequality is equivalent to `2 * G.indepNum ≤ Fintype.card α + (alphaCore G).card`. Connectedness is in the frozen type and is unused by the known bound.

## Mathematical sources

András Hajnal, *A theorem on k-saturated graphs*, Canad. J. Math. 17 (1965) 720–724. Clique-collection form: for a nonempty family Γ of maximum cliques, `|∩Γ| ≥ 2ω(G) − |∪Γ|`.

Vadim E. Levit and Eugen Mandrescu, *A set and collection lemma*, arXiv:1101.4564, https://arxiv.org/pdf/1101.4564. Corollary 2.3: for nonempty `Λ ⊆ Ω(G)`, `2α(G) ≤ |∩Λ| + |∪Λ|`. Corollary 2.4: `2α(G) ≤ |core(G)| + |corona(G)|`, where `core(G)` is the intersection of all maximum independent sets and `corona(G)` their union. The paper attributes the clique form to Hajnal and notes that Corollary 2.3 is the complementary independent-set form. Retrieved 2026-09-13.

The deletion definition of `alphaCore` matches Hajnal/Levit–Mandrescu `core(G)` after a proved equivalence: `α(G − v) < α(G)` if and only if `v` lies in every maximum independent set. That equivalence is part of the formalization, not an assumed redefinition.

WOWII list: http://cms.dt.uh.edu/faculty/delavinae/research/wowII/ (also the UHD mirror used by other WOWII files). Conjecture 101 is recorded in the Formal Conjectures source as a known inclusion-exclusion consequence.

The worker prompt’s finite-family induction (`|I ∪ (S ∩ U)| ≤ α` implies intersection loss is at most union gain) is the same cardinality content as Corollary 2.3. It is the implementation route. Levit–Mandrescu’s matching form (Lemma 2.1) is stronger and is not required.

## Public exact Lean search (2026-09-13)

Searches below found **no completed exact public Lean proof** of this frozen type or of Hajnal’s independent-set/core-corona inequality. Absence in these sources is not a proof of universal absence.

- Live DeepMind file: still `sorry`. History of `GraphConjecture101.lean` on `google-deepmind/formal-conjectures` (three commits, first `c270a997`); no later proof commit.
- GitHub issue/PR search on `google-deepmind/formal-conjectures` for `GraphConjecture101`, `conjecture101`, `WOWII101`, `alphaCore`, `alpha-core`, and independence-core: no proof PR. Issue 4573 is WOWII 59, unrelated. Hajnal hits are Erdős–Hajnal problems, a different theorem.
- GitHub code search `GraphConjecture101`: only the Formal Conjectures source file.
- GitHub repository search `wowii 101`, `wowii-graph-conjecture-101`: no repo.
- KitaKen1 public repos: WOWII 2, 31, 217, not 101. WOWII31 is excluded (prior exact Lean by KitaKen1, DeepMind PR 4658).
- Other WOWII Lean repos located by name (2, 31, 40, 59, 63, 85, 91, 109, 144, 160, 198a, 200, 217, 291, 322) are different statements.
- AlphaProof Nexus results: `gh api search/code?q=repo:google-deepmind/alphaproof-nexus-results+GraphConjecture101` empty. Nexus does contain GraphConjecture2, a different target.
- Epoch `LeanOpenProblems-results`: same query empty.
- Local Mathlib 4.33.1 `SimpleGraph` search: `indepNum`, `IsNIndepSet`, `indepSetFinset`, `isNIndepSet_induce`, `exists_isNIndepSet_indepNum` exist. No Hajnal collection lemma, no `alphaCore`/`core`/`corona` of maximum independent sets.
- `FormalConjecturesForMathlib` independence helpers do not contain this inequality.

Second pass immediately before the candidate claim (2026-09-13T01:41Z): issue/PR searches for `GraphConjecture101` and `Graph Conjecture 101` on DeepMind still empty; repository search `wowii-graph-conjecture-101` empty; live source SHA unchanged; Epoch `LeanOpenProblems-results` code search total_count 0; Nexus code search total_count 0 after a 429 retry. No exact public Lean proof of this frozen type was located. That is not a proof of universal absence.

## Excluded neighbour

WOWII31 is a different theorem (induced-path versus radius). An earlier exact public Lean proof exists; this worker must not repeat it.
