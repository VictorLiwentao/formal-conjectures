# Replacement screening 03: Green66 known quarter-power bound

Screened 2026-09-13 UTC for cursor-07-r03. This is known mathematics, separately declared as a research-solved variant, not a resolution of Green66's open fixed constant 1/10 question. No completed exact public Lean proof was located in the bounded sources below.

## Exact target and meaning

- Declaration: `Green66.green_66.variants.trivial_bound`.
- [Frozen source](https://github.com/google-deepmind/formal-conjectures/blob/a2f4a1bb12a28e04a969da78feefac7d1ce49565/FormalConjectures/GreensOpenProblems/66.lean).
- SHA-256: `d38ab7e233260302ef58121037a02dc94866ddae820e9fc84308ce7264e07acb`.
- Lean v4.33.1; campaign dependency pins unchanged.

There exists one positive real constant C such that for all sufficiently large real X, some natural sum of two natural squares lies in [X−C X^(1/4), X]. Eventual quantification handles small/negative X; C must be uniform, not depend on X. The worker must prove this entire existing declaration, not the open answer wrapper or merely an integer-X variant.

## Mathematical source and route

[Ben Green, A list of open problems](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#page=32), problem66 on printed page32 / PDF index31, describes the successive greatest-square argument. Credit the classical estimate and Green's exposition without attributing its discovery to the worker. Any more specific original-author claim must be supported by inspected sources.

Use either real floor square roots or N=naturalFloor(X), a=Nat.sqrt N, r=N−a², b=Nat.sqrt r. The two remainder bounds yield n=a²+b²≤X and a deficit bounded by a fixed constant times X^(1/4). A generous constant C=10 avoids unnecessary optimization. Prove all floor/cast/nonnegativity and nested-sqrt/rpow conversions. Mathlib tools include Nat.sqrt_le', Nat.lt_succ_sqrt', and Nat.sqrt_le_add. The mathematical route is checked; no Lean implementation was attempted during screening.

## Public exact-Lean screen

- Live DeepMind file still has sorry; this alone says nothing about external proofs.
- All-state searches by exact declaration/file and equivalent mathematical terms found statement PRs [4398](https://github.com/google-deepmind/formal-conjectures/pull/4398) and [1729](https://github.com/google-deepmind/formal-conjectures/pull/1729); actual patches inspected, not exact proof implementations.
- No exact target hit in [AlphaProof Nexus](https://github.com/google-deepmind/alphaproof-nexus-results) at `0647711a71183c1ea492ad60860776617ce1ea88`, or [Epoch results](https://github.com/epoch-research/LeanOpenProblems-results) at `8669ff224d86543fcc3ce192b2768ce175b734dd`; local HEADs matched live remote HEADs.
- Related public code DOES exist: [LeanGenius Erdos222Problem.lean](https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/Erdos222Problem.lean) introduces `bambah_chowla_upper_bound` as an extra axiom. Downstream lemmas relying on it are not admissible proofs of this target.
- Related Epoch OEIS275409 attempt, run `oeis-lite-200usd-grok46-j6r2uynasidzofcj`, `Submission/Spec.lean` around line11939, contains a lemma named `bambah_chowla`. Its actual conclusion is a weaker O(sqrt X) FORWARD interval bound. Statement and proof inspected, not compiled; it does not establish this fourth-root backward interval target.
- Mathlib SumTwoSquares.lean and Data/Nat/Sqrt.lean supply ingredients but no exact matching bound was found.
- Repository and equivalent-mathematics searches found no qualifying exact proof. Some later GitHub code searches hit rate limits; coverage is bounded, not a universal absence guarantee. Repeat the search before substantial work and final claims.

## Ownership and exclusions

The same worker owns equivalent fourth-root sum-of-two-squares gap bounds, including Green66, Erdos222 formulations, and OEIS A001481/A256435 aliases for this mathematical bound. Whole unrelated conjectures on those sequence pages are not automatically assigned. No overlap with current Cursor/Codex assignments was found. WOWII31 and WOWII101 are retired exclusions; remaining non-OEIS source prefixes stay reserved to this slot to prevent duplicate discovery work, but only the named Green66 variant is assigned.
