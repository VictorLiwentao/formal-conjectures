# cursor-07-r05 bounded replacement screen — WOWII7

Screen date: 2026-09-13 UTC. Recommendation: **WOWII7**, a substantive known-mathematics formalization candidate. No exact or sufficient stronger public Lean proof was located in the bounded searches below. This is not a universal absence certificate or a mathematical priority claim. Source and mathematical proof fit; finite-graph construction and spanning-tree interfaces remain engineering risks. Reserve only after predecessor WOWII20 passes audit and is stopped.

## Frozen exact target

- Target ID: `WOWII7`.
- Declaration: `WrittenOnTheWallII.GraphConjecture7.conjecture7`.
- File: `FormalConjectures/WrittenOnTheWallII/GraphConjecture7.lean`.
- Baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
- Toolchain: `leanprover/lean4:v4.33.1`.
- Full-file SHA256: `b24ee6ea69c547654647cdad7102ce95e64dc8a455fbd9aa12f7214b3d3c3968`.
- Today's current public raw source has the identical SHA256.
- Stable source: https://github.com/google-deepmind/formal-conjectures/blob/a2f4a1bb12a28e04a969da78feefac7d1ce49565/FormalConjectures/WrittenOnTheWallII/GraphConjecture7.lean

```lean
namespace WrittenOnTheWallII.GraphConjecture7
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
@[category research solved, AMS 5]
theorem conjecture7 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    ((maxL : ℤ) - 1 + (Fintype.card α : ℤ) - 2 * (G.indepNum : ℤ) : ℝ) ≤ Ls G := by
  sorry
```

Intended meaning: a finite connected simple graph on at least two vertices has a spanning tree with at least n+μ−2α−1 leaves, where α is the independence number and μ is maximum neighborhood independence. The lower expression uses integer subtraction, then a real cast; no truncated natural subtraction. `max'` is on the finite nonempty image of all vertices. `Ls` is a real supremum over spanning subgraphs whose coercions are trees, counting vertices of subgraph-degree exactly one; it is not maximum degree, arbitrary tree leaves, or induced-tree order. Definition: `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/SpanningTree.lean`. Establish an actual spanning-tree witness and the boundedness of the supremum. The small n=2 case and a nonpositive lower expression are legitimate boundary cases, not the whole target.

## Mathematics and strategy

Primary authors: Ermelinda DeLaVina, Siemion Fajtlowicz, Bill Waller, *On Some Conjectures of Griggs and Graffiti*, March 2002, revised May 2003. Author-institution-hosted PDF: https://www.uhd.edu/documents/academics/sciences/griggsngraffiti.pdf . Its Conjecture 2 (printed p2), proved using Lemma 1 (pp4–5), is exactly this inequality; its internal numbering differs from WOWII7.

Proof route: start with an independent neighborhood set M of size μ and its center c. Grow the connected set T=M∪{c}. Until M is maximal independent, connectedness supplies an edge uv with u neighboring M and v outside its closed neighborhood. Add v to M and u,v to T. Maintain |T|≤2|M|−μ+1 and connectivity. Termination gives domination, and |M|≤α. Take a tree on T and attach each remaining vertex as a leaf. Hence Ls≥n−|T|≥n−2α+μ−1. Treat μ≤1 separately, or verify that the same construction works from a one-neighbor seed.

Implementation judgment: prefer finite-set induction or a maximal feasible pair to avoid explicit recursive algorithms. The central obligations are connectivity through vertex insertion, independent-set cardinality, termination, attaching external leaves, and transport between induced-graph/subgraph APIs. A direct maximal-T variant may stop once T dominates, with one new independent vertex per at-most-two-vertex extension. This suggested adaptation is not already formalized. Do not cite the historical paper's informal equivalence between connected dominating sets and *exact* leaf complements without handling exceptional small graphs; only the safe inequality “at least n−|T| leaves” is needed.

The original WOWII portal in the frozen file is http://cms.dt.uh.edu/faculty/delavinae/research/wowII/ . That obsolete portal was not reliably retrievable. The author-hosted paper independently supplies the exact invariant definitions, inequality and proof. Preserve the collective 2026 source copyright. Credit these authors for mathematics, the original collective Lean formalizers, and Wentao Li only for actual new proof development/write-up; disclose AI assistance.

## Public Lean screen and limitations

Authenticated GitHub searches on 2026-09-13 used no open-state restriction:

- All-state `repo:google-deepmind/formal-conjectures "GraphConjecture7"`: one hit, import-only PR3820, https://github.com/google-deepmind/formal-conjectures/pull/3820 .
- All-state `"conjecture7" "leaves"` in DeepMind: zero.
- All-state `"Griggs"` in DeepMind: zero.
- All-state `"local independence" "leaves"`: only PR3820.
- All-state `"connected domination"`: PR3726 (unrelated Mukwembi counterexample), and WOWII2 PR4565 / issue4564. WOWII2 is a different average-local-independence bound, not the exact n+μ−2α−1 result.
- Repository searches `WOWII7` and `wowii-7`: zero.
- Code searches `"Griggs" language:Lean`, `"Griggs" "Fajtlowicz" language:Lean`, `"connected dominating" "independence" language:Lean`, `"connectedDominationNumber" "indepNum" language:Lean`, and `"conjecture7" "Ls" language:Lean`: zero. GitHub indexing can miss differently named or unindexed proofs; these are bounded negative results.
- Web searches of the exact declaration and mathematical names found the admitted upstream/mirror statement, the original paper, and unrelated graph developments. No exact public candidate was located and no such candidate was compiled.

Reproducible search entry points:
https://github.com/search?q=repo%3Agoogle-deepmind%2Fformal-conjectures+%22GraphConjecture7%22&type=issues
https://github.com/search?q=%22Griggs%22+language%3ALean&type=code
https://github.com/search?q=%22connectedDominationNumber%22+%22indepNum%22+language%3ALean&type=code

Result clones both match live remote HEAD today:

- AlphaProof Nexus: https://github.com/google-deepmind/alphaproof-nexus-results/tree/0647711a71183c1ea492ad60860776617ce1ea88
- Epoch: https://github.com/epoch-research/LeanOpenProblems-results/tree/8669ff224d86543fcc3ce192b2768ce175b734dd

Targeted Lean-file search for `GraphConjecture7`/`conjecture7` with word boundaries, Griggs, and connected-domination/independence combinations found no hits. Local Mathlib/project graph searches found the definitions of `Ls` and `connectedDominationNumber`, not the strengthened bound.

Related usable public development, **not exact coverage**: Nexus's `APNOutputs/AICollaborator/Graphs/GraphConjecture2.lean` proves Ls≥2(average neighborhood independence−1). Its checked declaration list and relevant proof regions concern double counting and neighbor-union leaf bounds, not global α or the connected-dominating-set estimate here. It may contain useful spanning-tree infrastructure. If reused, inspect dependencies, license and credit its authors rather than presenting their Lean code as original. Public c5-k4 work on WOWII183 contains connected-domination certificates and limited structural cases; the surfaced material did not state the universal strengthened Griggs bound. A worker must stop and reconcile if deeper inspection locates a sufficient general proof.

## Ownership / equivalence group

Read SUPERVISION.md, assignments.json, RESULTS.md and replacement-screening-05.md. This target has no equivalent among current OEIS/Codex reservations (A108081, A135508, A063880, A108866/A332786/A330718, A079727, A003161/A003162, A069004, A001818/A002454/A356041). It is different from excluded WOWII31, WOWII101, WOWII20 and Green66/A001481/A256435/Erdos222.

Reserve together: WOWII7; strengthened Griggs/Graffiti leaf bound `Ls≥n+μ−2α−1`; equivalent connected domination bound `γ_c≤2α−μ+1` (with small-case conditions tracked); DeLaVina–Fajtlowicz–Waller paper's Conjecture 2/Lemma 1. The weaker Griggs bound Ls≥n−2α+1 alone is not the same theorem and does not cover μ>2. Related WOWII2 remains prior public mathematics/formalization, not newly assigned work.

## Other candidates rejected during this pass

- WOWII17: prior formal-proof PR4161, https://github.com/google-deepmind/formal-conjectures/pull/4161 .
- WOWII23/32/34: active source-meaning corrections PR5736/5729/5733; do not exploit the frozen distance-average mismatch.
- WOWII36: prior exact disproof PR4572.
- Erdos387 easy divisor bound and Erdos1150 Parseval bound: already proved directly in frozen source.
- Erdos828 totient classification: explicit existing formal-proof link in frozen source.
- Erdos1026 upper bound: actual `exists_seq_with_monotone_subseq_sum_le` and stronger sharpness constructions in https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1026.lean . Public theorem bodies inspected, not recompiled. Reject despite absent exact declaration search hits.
- Erdos367 k≤2: actual `strong_bound_k1`/`strong_bound_k2` in https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/Erdos367Problem.lean . General lower-bound public developments also exist. Do not recommend the small variants as new formalization.
- Erdos1063 exception/factorial variants: prior solve PR3311/2795.
- Erdos1136 Mueller/optimality variants: actual public `A_density_half` and `sumfree_upperDensity_le_half` in https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos1136.lean .
- Erdos1148 weaker bound: prior solve PR3341/2825/3618.

Only this screen and the requested r05 prompt were written. No assignment register, worker source, branch, commit, launch, publication or spending setting was changed.
