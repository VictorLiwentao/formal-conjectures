# Independent audit: cursor-07-r04 / WOWII20

Audit date: 2026-09-13T03:40:24.135840+00:00

## Status

**PASS: independent fresh compilation, exact-type equivalence, nonvacuity and axiom audit.** Known mathematics formalization only; `novel_mathematics=false`. The final transitive axiom closure printed by the freshly compiled candidate is exactly `{propext, Classical.choice, Quot.sound}`. No open-problem resolution or first-formalization priority is claimed.

## Immutable inputs

- Frozen baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
- Worker seed: `7a37b78ee539aab88ebbb77a2579f838e9fcc7a6`.
- Audited candidate tip: `7fe9aa0477c5e82be229733008d5db098bf7017a`, `origin/cursor/b01-cursor-07-r04-9d2b`.
- Frozen source: `FormalConjectures/WrittenOnTheWallII/GraphConjecture20.lean`.
- Source SHA256: `969908dc9e73fd3ebea73cdf272df476583efbe9745185fd466726c5d4faa2e7`.
- Candidate: `research/batches/b01/workers/cursor-07-r04/targets/WOWII20/WOWII20.lean`.
- Candidate SHA256: `598c0a6231dbf61e68ded32dc047193c2149554d1b222caf28397cb1a719365c`.
- Original declaration: `WrittenOnTheWallII.GraphConjecture20.conjecture20`.
- Candidate declaration: `WOWII20.conjecture20`.
- Isolated scratch/logs: `/Users/wentaoli/Research/cursor07-r04-wowii20-audit-_j3_md01`.

The exact worker files and frozen source were extracted using `git show` into scratch. Every extracted file hash is retained in `source-hashes.json`. `environment-checks.json` confirms seed-to-tip edits are confined to the assigned worker folder, and frozen source/support/toolchain/manifest files were not changed. Live upstream main source was retrieved afresh and has the same source hash.

Worker STATUS/HANDOFF accurately label this a self-audited candidate awaiting independent review; their earlier candidate commit is historical. The immutable tip/hash above identifies what this audit actually compiles. Final documentation tip `dadf30cc901feb22fce0ba0bd200c5453266ac7a` was independently compared with the audited tip: only HANDOFF.md and the two-line prose correction in proof.md differ; all Lean files are unchanged. The candidate SHA256 was rechecked at the final tip and is identical. No recompile is needed for those prose-only changes.

## Independent build and trust checks

The frozen source and candidate were freshly compiled on Lean 4.33.1, producing isolated oleans. The cache `/Users/wentaoli/.codex/worktrees/1974/formal-conjectures` was used read-only for library dependencies. Its toolchain, lakefile, manifest, all frozen utility/support source files, and all nine manifest package HEADs match the baseline. Mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474`.

Reproduction from the scratch directory:

```sh
export LEAN_NUM_THREADS=2
export LEAN_PATH="$(cat lean-path.txt)"
/Users/wentaoli/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean -o FormalConjectures/WrittenOnTheWallII/GraphConjecture20.olean FormalConjectures/WrittenOnTheWallII/GraphConjecture20.lean
/Users/wentaoli/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean -DwarningAsError=true -o research/batches/b01/workers/cursor-07-r04/targets/WOWII20/WOWII20.olean research/batches/b01/workers/cursor-07-r04/targets/WOWII20/WOWII20.lean
/Users/wentaoli/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean -DwarningAsError=true ExactTypeAudit.lean
```

`compile-0.log`: source exit 0, with its single expected upstream `sorry` warning. The original admitted source is compiled with default warning handling. `compile-1.log`: candidate exit 0 with warnings-as-errors, including:

```text
'WOWII20.conjecture20' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The candidate does not import the original conjecture module at all. It imports the unchanged ForMathlib induced-graph API, Mathlib Chebyshev, and Mathlib tactics. Its final transitive closure excludes `sorryAx`, native decision/compiler trust axioms, and all other extra axioms. The only disabled lint options concern unused section variables, unused simp arguments and `haveI` style. No kernel checks or original definitions are disabled or replaced.

The auditor's `ExactTypeAudit.lean` imports both newly compiled modules, compares `ConstantInfo.type` using `Lean.Meta.isDefEq`, and reprints candidate axioms. It also checks that the complete graph on `Fin 2` is connected, using `SimpleGraph.connected_top`; `Fin 2` supplies the finite/nontrivial type instances. The command exited 0; `compile-2.log` prints `PASS: exact frozen theorem type is definitionally equal to candidate type` and the allowed three axioms. This confirms the graph hypotheses are satisfiable. The comparison uses the full polymorphic declaration types from `getConstInfo`, with the same rigid `u_1` level parameter; it does not specialize the target to `Fin 2` or any fixed universe. The concrete graph example is a separate nonvacuity check.

## Statement and mathematical audit

The intended type preserves every binder and definition:

```lean
{α : Type u} [Fintype α] [DecidableEq α] [Nontrivial α]
(G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
  let deg_avg : ℝ := (∑ v, (G.degree v : ℝ)) / (Fintype.card α : ℝ)
  (Fintype.card α : ℝ) / (⌊deg_avg⌋ : ℝ) ≤ (SimpleGraph.b G : ℝ)
```

The floor is `Int.floor` of a real average, then cast to real. `b G` is unchanged: the real cast of the natural supremum of vertex-set cardinalities inducing a bipartite graph. The candidate's `le_b` proves the feasible-set membership and boundedness needed to use this supremum, rather than exploiting an unbounded/default supremum. The unchanged 2-coloring equivalence really colors all induced edges.

Let `w_G(v)=min(1,2/(degree(v)+1))`. The candidate proves for every finite simple graph that some induced bipartite vertex set has cardinality at least the total weight:

- For a vertex of degree at most 1, delete it, use induction, and reinsert it. The retained neighbors' weights cannot decrease; the removed weight is at most 1. A direct two-color extension handles the sole possible retained neighbor.
- If all degrees are at least 2, delete a maximum-degree vertex of degree `D`. Each neighbor of degree `t≤D` gains `2/(t(t+1)) ≥ 2/(D(D+1))`. With exactly `D` neighbors, the total gain is **at least** the removed weight `2/(D+1)`. Non-neighbor weights are unchanged. Induction then gives a sufficient set without reinserting the deleted vertex.
- Empty graph and subtype cardinal reductions are handled explicitly. Lifting an induced set back to the original graph preserves cardinality and its 2-coloring.

In a connected nontrivial graph, all degrees are at least 1 and the average is at least 1, so clipping disappears. Chebyshev applied to reciprocal degree-plus-one and degree-plus-one proves `sum w ≥ 2n/(average+1)`.

For average at least 2, write `k=floor(average)`. The proof establishes `k≥2`, positive denominators, and `average+1≤2k`; therefore `n/k≤2n/(average+1)≤b(G)`. For average below 2, integer edge count plus connectedness gives exactly `n−1` edges, hence a tree. The graph is bipartite, `b(G)≥n`, and the floor equals 1. Thus there is no zero-denominator, empty-domain, changed-floor or disconnected-graph loophole.

The arithmetic, induced-subgraph definition, quantifier order and graph hypotheses match the frozen mathematical claim. The implementation directly constructs a bipartite induced set with the AKS bound; it does not purport to formalize all induced-degeneracy results of the cited paper.

## Prior mathematics and bounded public-Lean review

Primary evidence was read afresh on the audit date: [Alon–Kahn–Seymour, Large Induced Degenerate Subgraphs (1987)](https://web.math.princeton.edu/~nalon/PDFS/Publications/Large%20induced%20degenerate%20subgraphs%20in%20graphs.pdf). The paper defines d-degeneracy using degree strictly below d, so its d=2 case is a forest. Theorem 1.3 supplies the weighted bound; its page-208 induction is the deletion argument used here. Corollary 1.4 supplies `2n/(average+1)` for average at least 2. These facts, plus the elementary tree/floor cases, establish prior mathematical coverage. [Alon–Mubayi–Thomas](https://www.cs.tau.ac.il/~nogaa/PDFS/amt4.pdf) is a further relevant induced-forest reference. No Graffiti/WOWII solver identity is inferred from these references.

Current bounded searches are preserved in `public-search.json` and `additional-search.json`, with read artifacts under `search-hits/`. They include all-state DeepMind issue/PR queries for GraphConjecture20, WOWII 20, induced forest and Kahn; exact namespace/code searches; AKS and induced-forest/bipartite-degree equivalents; Epoch results; AlphaProof Nexus results; and local Mathlib/ForMathlib graph sources.

Findings:

- No exact GraphConjecture20 proof PR was found. Induced-forest PR hits concern different WOWII counterexamples; Kahn hits concern unrelated problems.
- Global GraphConjecture20 search contains many `GraphConjecture200` prefix hits, catalog records and source copies. The exact raw source copy in MarceloClaro/OpenCode_Ecosystem was fetched and still admits the theorem.
- [FormalConjectures-Bench's exact target](https://github.com/AllenGrahamHart/FormalConjectures-Bench/blob/0d031f7212150df788f4fa38c26cfc3fc729f3d0/tasks-v2/writtenonthewallii-graphconjecture20-conjecture20/environment/data/FormalConjecturesBench/Target.lean), its golden target, solve script and type wrappers were fetched and read. The targets contain `sorry`; the script says no reviewed solution is bundled; the wrappers do not prove the theorem.
- Both tadamcz/fc-review-results records were fetched; they contain the admitted source and review data, not an exact proof.
- An additional [jt496/extremal_graph Lean3 induced.lean hit](https://github.com/jt496/extremal_graph/blob/1bfb63ed1f6ca633d1ee4e1846f429cfe32c6a83/src/induced.lean) was fetched and read. Its “induced bipartite” wording refers to cut-edge graphs and degree/edge decomposition for different results; it contains no weighted AKS or corresponding induced-vertex lower bound.
- Global Lean searches for AKS weight and Kahn/Seymour found no matching proof. Induced-forest hits were definitions/source copies. Local Mathlib/ForMathlib search likewise found the induced-size definitions and coloring API, not the weighted lower bound. Epoch/Nexus searches for conjecture20 returned no matches.

No prior completed exact or sufficiently strong public Lean proof was located in this bounded review. This is not a universal absence guarantee: GitHub indexing, alternate names, private/unindexed work and later additions limit any priority inference. The admitted/review/unrelated artifacts above were not compiled as competing proofs because their inspected types/content do not supply the target.

## Credits and documentation

The candidate preserves the collective Formal Conjectures Authors copyright, names the collective as original statement formalizers (2025), and names Wentao Li for 2026 proof development/write-up. It credits Alon, Kahn and Seymour for the known mathematics and discloses Cursor/Grok assistance. It makes no new-mathematics claim.

Non-blocking documentation correction at audited tip: `proof.md` says the total neighbor gain “equals” the deleted weight. The proof establishes that it is **at least** the deleted weight; equality need not hold for neighbors with degree smaller than the maximum. This wording was corrected in final documentation tip `dadf30cc901feb22fce0ba0bd200c5453266ac7a`; the corrected text says “is at least.” All Lean terms are unchanged.

## Limits and write scope

The independent audit reuses matched Mathlib/support library oleans; it does not rebuild the entire dependency tree. All candidate/source outputs are fresh and isolated. No worker files, shared cache, A069004 audit process/files, original source files or repository branches were modified by this audit. The only coordinator artifact written is this report. No commit, push, publication or PR was performed.

## Coordinator final documentation check

Final worker tip `dadf30cc901feb22fce0ba0bd200c5453266ac7a` contains only the requested proof.md wording correction and its HANDOFF record relative to the audited tip. The candidate Lean SHA256 is unchanged (`598c0a6231dbf61e68ded32dc047193c2149554d1b222caf28397cb1a719365c`). The Cursor UI confirms an empty continuation-timer list, inactive goal, and cessation. The correction is complete; this does not change the PASS result.
