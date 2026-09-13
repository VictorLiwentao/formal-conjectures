# Independent audit: cursor-07-r02 / WOWII101

Audit date: 2026-09-13 UTC. Only isolated scratch files were written; worker,
coordinator, source, dependency, and cache files were not modified.

## Technical verdict

**Candidate fresh compilation PASS, exit 0 with warnings-as-errors.** Source module
fresh compilation passed. The exact-type example compiled and both signatures print
identically apart from the irrelevant connectedness binder name. Final transitive
axiom output:

```text
'WOWII101.conjecture101' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This excludes `sorryAx`, compiler/native-evaluation trust, and custom axioms. The
imported admitted source theorem is not a dependency of the candidate proof.
Mathematical source/type inspection: passed. Novel mathematics: false.
No earlier completed exact or equivalent public Lean proof was identified in the
independent searches below. This does not establish first-formalization priority.

Worker commit: `b42564b6f4e04abf0256355f53000056e2c2c924`.
Frozen source commit: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
Coordination seed: `dc6f750f34db0ca579f76bc358082157072f2083`.
Proof path: `research/batches/b01/workers/cursor-07-r02/targets/WOWII101/WOWII101.lean`.
Proof SHA-256: `5018f7ba7f2ec8b63d4334b606d8936db097e635f9c959c3d2877ae9dee8e34a`.
Source path: `FormalConjectures/WrittenOnTheWallII/GraphConjecture101.lean`.
Source SHA-256: `870cd77d2cb8bf98fcbe4bdeee7c52620009af97368fc4358dc595af716046c6`.
Live upstream source retrieved during this audit has the same source hash.

The worker theorem `WOWII101.conjecture101` proves the frozen declaration
`WrittenOnTheWallII.GraphConjecture101.conjecture101` with exact type:

```lean
∀ {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected),
  G.indepNum ≤ (Fintype.card α +
    (WrittenOnTheWallII.GraphConjecture101.alphaCore G).card) / 2
```

The original `alphaCore` and `indepNumDeleteVertex` definitions are imported,
not changed or replaced. The candidate contains an exact-type example applying
its theorem and `#check`s both candidate and original signatures. The different
binder names `h` and `_h` have no mathematical effect. The original theorem is
not applied. There is no sorry/admit/native_decide/custom axiom in the candidate.
The core/intersection equivalence is proved, not postulated.

## Independent reproduction

Scratch directory: `/Users/wentaoli/Research/cursor07-r02-wowii101-audit-i562iww5`.
Exact bytes extracted using `git show <worker-commit>:<file>`.
Lean binary: `/Users/wentaoli/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean`.
`LEAN_NUM_THREADS=2`. Exact `LEAN_PATH` retained in `lean-path.txt`: scratch first,
then read-only `.lake/build/lib/lean` and package `.lake/build/lib/lean` paths
under `/Users/wentaoli/.codex/worktrees/1974/formal-conjectures`.

The read-only cache checkout's utility/library/toolchain/manifest source paths
match the frozen baseline. All nine package checkout HEADs match the manifest;
Mathlib is `0df444a360eaa60ab8c11dca51a86af692955474`.
No full dependency rebuild was necessary. The untouched admitted source module
was freshly compiled into the isolated scratch path before the proof:

```sh
lean FormalConjectures/WrittenOnTheWallII/GraphConjecture101.lean -o FormalConjectures/WrittenOnTheWallII/GraphConjecture101.olean
lean -DwarningAsError=true research/batches/b01/workers/cursor-07-r02/targets/WOWII101/WOWII101.lean
```

Source compile exit 0; its single expected warning is the untouched target's
`sorry`. Source log: `GraphConjecture101.log`. Candidate log: `WOWII101.log`.
Two cosmetic linters are disabled in the candidate (unusedSectionVars and
moduleDocstring); kernel checking and axioms are unaffected.
The standalone worker audit file was read, but need not be rebuilt because
this candidate file itself includes the exact-type example and both `#check`s.

Scope check: diff from coordination seed contains only
`research/batches/b01/workers/cursor-07-r02/`. Frozen source/library/dependency
paths have no changes versus baseline.

## Meaning and mathematical source

The invariant is the independence number of a finite simple graph. Source
`alphaCore` means the vertices whose deletion strictly decreases that number.
The proof establishes equivalence with membership in every maximum independent
set, using transport to and from the induced graph with that vertex removed.
Natural division is floor division; the final arithmetic step uses its correct
multiplication equivalence. Connectedness is retained in the exact wrapper but
unneeded by the stronger bound, which is appropriate rather than a loophole.
Nontrivial finite connected graphs exist, so the statement is not vacuous.

Independently read [Levit–Mandrescu, A set and collection lemma](https://arxiv.org/pdf/1101.4564),
Corollaries 2.3, 2.4, and 2.10. The independent-set family inequality is the
complementary form of Hajnal's clique collection result. Applying it to all
maximum independent sets gives the core/corona bound, and bounding the union
by all vertices yields this target. The worker's finite-family induction
correctly proves the same inequality through intersection loss versus union
gain. This is known mathematics, not a new conjecture resolution.

Credits are appropriate: Hajnal (1965), Levit–Mandrescu's independent-set/core
form, The Formal Conjectures Authors' statement formalization/copyright,
Wentao Li's Lean implementation and write-up, and explicit AI assistance in
`proof.md`. No claim of new mathematical discovery is made.

## Independent public proof and equivalence searches

Searches were run through GitHub's authenticated API without open/closed state
filters, plus web and local library searches. Records are preserved in
`public-search.json`, `equivalence-search.json`, and `search-hits/`.

- All-state DeepMind issue/PR queries `GraphConjecture101`, `conjecture101`,
  and `alphaCore`: zero results. Broad Hajnal query: 41 results, concerning
  different Erdős–Hajnal/infinite graph problems, not the finite core bound.
- Global code `GraphConjecture101`: six results. The upstream file is admitted;
  two `tadamcz/fc-review-results` records reproduce the admitted statement and
  discuss definition equivalence; `akakabrian/WOW-146` hit is an upstream build
  log; `weiyangzen/awesome_theorems` is a pending catalog review without fixed
  proof evidence; `vela-science/vela` is an axiom-census frontier record, with
  one declaration still needing proof, not a target proof artifact.
- Global Lean code `Hajnal`: five results, all other theorems/frameworks.
  Global `alphaCore language:Lean`: two copies of a WOWII443 finite graph
  counterexample, not this universal core inequality. They were read.
- `corona indepNum language:Lean` and `"maximum cliques" language:Lean`:
  no results. `corona language:Lean`: two linguistics-library files.
  `indepNum inf language:Lean`: 16 primarily Mathlib/library/fork/API results;
  none identified as a Hajnal family theorem. Local frozen Mathlib and
  FormalConjecturesForMathlib graph searches found no existing core/corona
  inequality or Hajnal family bound.
- Nexus and Epoch results code search for `GraphConjecture101`: zero results.
- Repository `wowii-graph-conjecture-101`: zero. Repository `Hajnal Lean`:
  Hajnal–Szemerédi and Erdős–Hajnal C5/P5 projects, different results.
- General web queries for exact filename and Hajnal maximum-independent-set
  Lean proof located no exact artifact. Very broad core/independent searches
  were noisy and only their first returned page was inspected; they are not
  asserted as exhaustive negative evidence.

Unlike WOWII31, no missed exact proof PR/artifact emerged from these checks.
Search indexing, default-branch coverage, unindexed branches, and private work
limit all absence claims. Final classification:
`independently_verified`, `known_mathematics_formalization`,
`no_prior_exact_public_lean_proof_found_in_checked_sources`. Do not replace
that bounded statement with an unconditional first-formalization claim.
