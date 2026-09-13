# Replacement screening 02: non-OEIS WOWII101

Screened 2026-09-13 UTC for cursor-07-r02. This is known mathematics, not a newly open conjecture. No completed public exact Lean proof was found in the bounded sources below; absence is not certified globally.

## Assigned statement and mathematical fit

Frozen source: [GraphConjecture101.lean](https://github.com/google-deepmind/formal-conjectures/blob/a2f4a1bb12a28e04a969da78feefac7d1ce49565/FormalConjectures/WrittenOnTheWallII/GraphConjecture101.lean).
Declaration: `WrittenOnTheWallII.GraphConjecture101.conjecture101`.
SHA-256: `870cd77d2cb8bf98fcbe4bdeee7c52620009af97368fc4358dc595af716046c6`.
Toolchain remains Lean v4.33.1.

For a finite connected graph, independence number is at most floor((vertex count + alpha-core size)/2). The source alpha-core uses a strict decrease of independence number on vertex deletion. Its equivalence to the intersection of all maximum independent sets must be proved, not assumed.

[Levit–Mandrescu, primary paper](https://arxiv.org/pdf/1101.4564), Corollary 2.4, states `2α(G) ≤ |core(G)| + |corona(G)|`. This follows from Hajnal's clique collection lemma in the complementary independent-set formulation. Bound corona by all vertices. Credit Hajnal and the actual proof source used. The finite-family induction route in the worker prompt was mathematically checked but has not been Lean-tested. Main implementation risks: independence-number transport under induced subgraphs and finite-set intersection/union bookkeeping.

The frozen source already marks this research solved. Connectedness is unnecessary to the known bound, so proving a stronger general graph lemma is legitimate provided the exact source type follows. This is distinct from WOWII31 induced paths/radius and all active OEIS/Codex mathematical groups. No source-definition loophole is being used.

## Bounded public screening

- Live DeepMind file still contains sorry. This alone establishes nothing about prior public formalization.
- All-state GitHub issue/PR searches for GraphConjecture101 and conjecture101 and broader 101 plus Wall/independence returned only the original [statement PR3820](https://github.com/google-deepmind/formal-conjectures/pull/3820) and unrelated entries, including issue4573.
- GitHub repository/equivalent-name searches for WOWII101, Hajnal clique collection lemma and independence core/corona found no exact proof. An axiomatized Hajnal–Szemerédi result is a different theorem, not evidence for this target.
- No exact-name/core hits in [AlphaProof Nexus results](https://github.com/google-deepmind/alphaproof-nexus-results) at `0647711a71183c1ea492ad60860776617ce1ea88`, or [Epoch results](https://github.com/epoch-research/LeanOpenProblems-results) at `8669ff224d86543fcc3ce192b2768ce175b734dd`. Both local result-clone HEADs matched remote HEADs when screened.
- No relevant completed Hajnal/core lemma found in the available local Mathlib graph source search.

These searches may miss equivalent statements under other names, unindexed repositories or very recent work. The worker must repeat the exact/equivalence audit before substantial work and again before a final claim.

## Predecessor and other candidates

WOWII31 worker proof compiled independently, but an earlier exact public Lean proof was found at [KitaKen1 immutable artifact](https://github.com/KitaKen1/wowii-graph-conjecture-31-lean/blob/a948e9fc07e11b786aee8dadb1376b4d938454d6/lean/GraphConjecture31.lean), linked in [DeepMind PR4658](https://github.com/google-deepmind/formal-conjectures/pull/4658). See audits/cursor-07.md for exact source/axiom evidence. No new-mathematics or first-formalization claim for this batch's WOWII31 implementation.

WOWII133's incomplete C4-free graph screening is preserved with the predecessor. It is not assigned to the successor: WOWII101 has a known elementary argument and a clearer formalization path. WOWII19/40/61/100 also remain unassigned and unscreened as replacements.
