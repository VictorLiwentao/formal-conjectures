# cursor-07-r04 replacement screen: WOWII20

Screened 2026-09-13 UTC. Recommendation: reserve for a bounded formalization attempt. This is **known mathematics needing a formal proof**, not a new mathematical discovery. No public exact or stronger sufficient Lean proof was located in the bounded search below; absence is not proved. Moderate graph-library engineering risk; substantially larger than the recent elementary Green66 bound. No backup survived comparable screening cheaply.

## Exact target and source

- Frozen baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
- File: `FormalConjectures/WrittenOnTheWallII/GraphConjecture20.lean`.
- Declaration: `WrittenOnTheWallII.GraphConjecture20.conjecture20`.
- SHA256 of full frozen file bytes: `969908dc9e73fd3ebea73cdf272df476583efbe9745185fd466726c5d4faa2e7`.
- Live GitHub contents checked today have exactly the same SHA256.
- Stable source: https://github.com/google-deepmind/formal-conjectures/blob/a2f4a1bb12a28e04a969da78feefac7d1ce49565/FormalConjectures/WrittenOnTheWallII/GraphConjecture20.lean
- Existing source status: `@[category research solved, AMS 5]`, proof is `sorry`.
- Preserve the existing 2025 Formal Conjectures Authors copyright notice. New files should include the root-requested collective 2026 and Wentao Li 2026 notices without rewriting upstream notices.

```lean
namespace WrittenOnTheWallII.GraphConjecture20
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
@[category research solved, AMS 5]
theorem conjecture20 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let deg_avg : ℝ := (∑ v : α, (G.degree v : ℝ)) / (Fintype.card α : ℝ)
    (Fintype.card α : ℝ) / (⌊deg_avg⌋ : ℝ) ≤ (b G : ℝ) := by
  sorry
```

Intended statement: every finite connected simple graph with at least two vertices has an induced bipartite subgraph containing at least n/floor(d) vertices, where d is the average degree. The floor is the integer floor cast to real, not floor of the quotient. Nontrivial excludes the n=1 corner, connectedness implies positive degrees and d≥1, so the denominator is positive. `b` is the real cast of the supremum of attainable finite induced bipartite vertex-set sizes, not an edge count or an arbitrary non-induced subgraph invariant.

Definition and usable existing bridges are in `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Induced.lean`: `largestInducedBipartiteSubgraphSize`, `b`, `induce_isBipartite_iff_exists_coloring`, and `largestInducedBipartiteSubgraphSize_eq_computable`. The finite supremum is bounded by n, and an explicit chosen vertex set supplies its lower bound. No need for exhaustive graph enumeration.

## Known mathematics and primary source

Alon, Kahn and Seymour, *Large Induced Degenerate Subgraphs*, Graphs and Combinatorics 3 (1987), 203–211, DOI https://doi.org/10.1007/BF01788542 . Author-hosted full paper: https://web.math.princeton.edu/~nalon/PDFS/Publications/Large%20induced%20degenerate%20subgraphs%20in%20graphs.pdf . Theorem 1.3 (printed p204) gives an induced forest of size at least Σ_v min(1,2/(deg(v)+1)); its induction proof is on p208. Corollary 1.4 (p205) gives size at least 2n/(d+1) for average degree d≥2. Their degeneracy convention calls forests 2-degenerate; the modern ≤r convention calls them 1-degenerate. Their own text notes the corresponding induced-colorable bounds.

Independent author-hosted confirmation of this corollary: Alon–Mubayi–Thomas, *Large induced forests in sparse graphs*, introduction, printed p2: https://www.cs.tau.ac.il/~nogaa/PDFS/amt4.pdf . This states the 2n/(d+1) bound and attributes it to AKS1987.

The original WOWII portal is cited by the frozen file as http://cms.dt.uh.edu/faculty/delavinae/research/wowII/ . Its obsolete host/current UHD alternatives were not reliably accessible in this bounded screen. Therefore the exact original solver of WOWII20 is not independently established here; credit the general mathematical bound to AKS1987, rather than inventing a WOWII20 solver attribution.

## Suggested Lean strategy (specialization/inference, not an existing Lean proof)

1. Prove a finite-graph lemma producing a two-colorable induced vertex set of size at least W(G)=Σ_v min(1,2/(deg(v)+1)). Work with explicit finite sets/colorings and induction on vertex count; one may avoid building a whole general degeneracy theory.
2. If G has a vertex v of degree at most one, delete it and apply induction. Every remaining degree weakly decreases, so W(G-v)≥W(G)-1. Reinsert v into the chosen induced set, giving it a color different from its sole possible neighbor. Thus size increases by one and two-colorability survives. This includes isolated vertices arising in recursive graphs; do not use the unclipped harmonic expression throughout induction.
3. Otherwise choose v of maximum degree D, with every degree at least two. Delete v and retain the chosen set from the smaller graph. A neighbor u of degree t contributes weight gain 2/(t(t+1)); since 2≤t≤D, each gain is at least 2/(D(D+1)). There are D neighbors, so the total gain offsets the deleted vertex's weight 2/(D+1). Therefore W(G-v)≥W(G). The clipped weight agrees with the reciprocal expression even when a degree-two neighbor falls to degree one. Lifting an induced coloring along deletion is routine but must be formalized.
4. On the original connected graph with n≥2 there are no isolated vertices, hence all weights equal 2/(deg(v)+1). Cauchy–Schwarz for positive numbers deg(v)+1 yields Σ1/(deg(v)+1) ≥ n²/Σ(deg(v)+1)=n/(d+1). Thus b(G)≥2n/(d+1).
5. For d≥2, let k=floor(d). Then k≥2, d<k+1, and d+1<k+2≤2k. Positivity implies n/k≤2n/(d+1), giving the exact target.
6. Handle d<2 separately: connectedness gives m≥n-1, while 2m<n·2 gives m<n, hence m=n-1 by integrality. A connected graph with exactly n-1 edges is a tree, hence bipartite. Therefore b(G)=n and floor(d)=1. Do not assert that an arbitrary graph of average degree below two is acyclic: connectedness is essential. The harmonic bound alone is insufficient in this corner.

The main work is the deletion/induction/coloring interface and finite weighted sums, not new mathematics. An alternative random-order averaging proof of the weight lemma exists, but would introduce unnecessary permutation/counting infrastructure if the deterministic induction fits the local APIs.

## Bounded public formalization search

Read current coordinator assignments and SUPERVISION before choosing the target. No active sequence group or previously completed task is equivalent. Explicitly excluded WOWII31, WOWII101, Green66, A001481/A256435/Erdos222 gap variants. Known all-active OEIS groups are unrelated to finite induced bipartite graph bounds.

GitHub searches used authenticated API search, without `is:open` or another state filter, so PR/issue searches covered all states. These URLs reproduce the logical queries, but search indices may change:

- https://github.com/search?q=repo%3Agoogle-deepmind%2Fformal-conjectures+%22GraphConjecture20%22&type=issues — 0.
- https://github.com/search?q=repo%3Agoogle-deepmind%2Fformal-conjectures+%22conjecture20%22&type=issues — 0.
- https://github.com/search?q=WOWII20&type=repositories — 0; broader WOWII+20 repository search previously found only unrelated `openmikasa/wowii-conjecture-200`.
- https://github.com/search?q=%22conjecture20%22+language%3ALean&type=code — 0 in earlier exact declaration search.
- https://github.com/search?q=%22Alon%22+%22Kahn%22+%22Seymour%22+language%3ALean&type=code — 0.
- https://github.com/search?q=%22induced+forest%22+language%3ALean&type=code — 2: upstream definitions and a copied definitions file in txmy/ultra-mathematician. Neither is the general bound.
- https://github.com/search?q=%22induced%22+%22averageDegree%22+language%3ALean&type=code — 0.
- Exact/general math web queries (`Alon Kahn Seymour Lean`, `induced forest Lean graph bound`) located math literature, unrelated WOWII counterexamples, and existing statement files, not a sufficient proof.
- Broader DeepMind `induced forest` all-state query had 6 hits: PR4634/4583/4514/4592, issue4573 (counterexamples to WOWII58/59/65/63/85), and import batch PR3796. Broader `bipartite average` had 5 hits: PR4634/3796/4482, issue4481 and unrelated quantum issue3437. These do not identify the weighted induced-forest bound. Broad `WOWII 20` had 9 noisy numeric hits, none titled a proof of target20. Exact phrase `Conjecture 20` is tokenized broadly and returned many unrelated numbered problems; do not interpret that query as an exact proof absence certificate.

Local Mathlib `Mathlib/Combinatorics/SimpleGraph` and project graph-library searches for induced forest, Kahn, Seymour, Caro–Wei and degeneracy found definitions but no general weighted induced-forest or average-degree bound. This was a targeted source search, not a semantic proof that no differently named theorem exists.

Both result clones matched current live remote HEAD today; Lean-file search for GraphConjecture20/conjecture20, induced-forest text and Alon–Kahn text had no hits:

- https://github.com/google-deepmind/alphaproof-nexus-results/tree/0647711a71183c1ea492ad60860776617ce1ea88
- https://github.com/epoch-research/LeanOpenProblems-results/tree/8669ff224d86543fcc3ce192b2768ce175b734dd

No candidate public proof script for WOWII20 or the sufficient AKS bound was found, hence none was compiled. This qualifies as **bounded no-located-public-proof**, not proven absence or priority clearance. A worker finding such a proof should stop/reconcile novelty immediately.

## Rejected alternatives during this screen

- Erdos261 infinitude: reject despite exact-name search misses. `rjwalters/lean-genius/proofs/Proofs/Erdos261Problem.lean` contains `borwein_loring_family` and `cusick_infinitely_many`, with relevant positive distinct finite-sum representation. https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/Erdos261Problem.lean . Not compiled here, but a substantive public equivalent candidate is enough to retire it.
- Erdos649 Tong variant: `tong_counterexamples` in https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos649.lean is a substantive public equivalent proof candidate.
- Mathoverflow75792 complexity_three_pow: exact public DeepMind PR2958.
- WOWII3/4/5/6: existing solve PR3158/3159/3160/3161 (and prior2634–2637).
- WOWII13: public source-scoped proof preprint for WOWII19 explicitly lists WOWII13 as a proved helper, https://www.preprints.org/manuscript/202607.0114 . Avoid without further prior-proof audit.
- WOWII133 remains the harder open structural graph problem already preserved by the worker; do not treat it as an easy fallback.

No coordinator files, source working trees, PRs or external task launches were changed by this screen.
