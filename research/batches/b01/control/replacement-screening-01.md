# Replacement screening 01

Date: 2026-09-12. Read-only mathematical screening against frozen upstream commit `a2f4a1bb12a28e04a969da78feefac7d1ce49565`; only this report was written. No proof, build, commit, PR or push was performed.

The updated user criterion permits **new Lean formalizations of known mathematics**, while still rejecting an already established Lean proof. This makes A109074 eligible for reconsideration. It does not make A052709 eligible: an accepted public Lean result was found in addition to its informal proof.

The checked assignment manifest reserves A237271, A108081, A076141, A135508, A063880, A108866/A332786/A330718, A079727, A003161/A003162, and the non-OEIS discovery scope. None of the two recommendations below belongs to those groups. A237271 and A076141 remain excluded as instructed even though their worker status is stale in the manifest.

## Recommendation 1: A069004 upper-bound disproof — finite certification work

- Exact primary declaration: `OeisA69004.conjecture2.variants.upper_bound_false`.
- Same-group corollary: `OeisA69004.conjecture2`. These are one assignment, not two independent results.
- Source file: `FormalConjectures/OEIS/69004.lean`.
- Frozen source SHA256: `c29abb2a5c1e48761cc6d7ebb4332bd728071b6ea6059263ffcf153800282ca2`.
- [Frozen source](https://github.com/google-deepmind/formal-conjectures/blob/a2f4a1bb12a28e04a969da78feefac7d1ce49565/FormalConjectures/OEIS/69004.lean).
- Statement: `¬ ∀ n : ℕ, 1 < n → Nat.primeCounting n ≥ a n`, where `a n` counts prime values of `n²+s²` for `1 ≤ s < n`.
- Known result: `a(512720)=42666` and `π(512720)=42493`, so the proposed upper bound fails. Credit the published counterexample in [upstream PR #5453](https://github.com/google-deepmind/formal-conjectures/pull/5453), author `j2d9w5xtjn-png`, which reports two independent deterministic computations and explicitly does not claim minimality. The original stronger conjecture is attributed to T. D. Noe, February 26, 2007 in [OEIS A069004](https://oeis.org/A069004).
- Status: **known computational disproof, candidate new completed Lean certification**; not new mathematics.

### Existing-Lean screen and significant caveat

Both exact declarations are still `sorry` in the frozen source. No matching Google/AlphaProof Nexus `.lean` result was found under `/tmp/math-google-results`. The Epoch snapshot has three `oeis_a069004_conjecture_2` runs, all score `I`, but **all three contain substantial apparent complete proof attempts**. The reasons recorded are one 1800-second timeout and two exit-137 kills, not a demonstrated mathematical gap. Thus this is not a claim that no Lean source exists: the potentially new contribution is a successfully completed, audited certificate. A longer or better-organized build of an existing attempt may already settle it. The worker must inspect that before describing its contribution as a new formalization.

Relevant public attempts:

- [OpenAI attempt](https://github.com/epoch-research/LeanOpenProblems-results/blob/main/runs/oeis-full-50usd-oai-jajpvieznaevpoyg/oeis_a069004_conjecture_2/Submission/Spec.lean): Pocklington database, 42,494 certified targets, timeout after 1800 seconds.
- [Anthropic attempt](https://github.com/epoch-research/LeanOpenProblems-results/blob/main/runs/oeis-full-50usd-ant-j0j0g4uzligm1k41/oeis_a069004_conjecture_2/Submission/Spec.lean): chunked certificate and prime-count computation, exit 137.
- [Google attempt](https://github.com/epoch-research/LeanOpenProblems-results/blob/main/runs/oeis-full-50usd-gdm-1s7vwp2si1ap0r6d/oeis_a069004_conjecture_2/Submission/Spec.lean): fast-primality bridge and direct computation, exit 137.

Live GitHub issue search for `A069004` found the status PR and one related review-pass PR, not an accepted proof. Repository searches for `A069004` and `oeis 69004` returned zero repositories. Web searches for `A069004 Lean`, `512720 Lean proof`, and the exact theorem name found no completed proof. This is a bounded negative search, not exhaustive novelty clearance.

Priority rationale: no unresolved mathematical discovery is necessary. There is a known finite witness and prior certificate work. However, proving tens of thousands of primality claims efficiently is engineering-heavy; this is not a one-line `decide` recommendation. A strict policy excluding any pre-existing proof script, even an uncompleted timed-out script, would reject this candidate.

### Quantification and certificate contract

The target negates a universal upper bound. It requires **one** natural `n > 1` such that `Nat.primeCounting n < a n`; it does not require a minimal counterexample, an exact value of `a n`, any assertion for infinitely many `n`, or a proof/disproof of the separate lower bound. At `n=512720`, it is enough to certify a list of **42,494 pairwise distinct** integers `s` in `Finset.Ico 1 512720` with each `512720^2+s^2` prime, together with `Nat.primeCounting 512720 ≤ 42493`. The sequence definition then gives `42494 ≤ a 512720`. Use the inclusive endpoint convention of `Nat.primeCounting`; a `Nat.count Prime` bridge needs the corresponding `512721` cutoff. The exact reported total 42,666 is unnecessary.

Do not launch a giant naive reduction of the full prime sum or trial-division tests. Inspect the existing Pocklington/chunked attempts first, preserve theorem-to-original-definition bridges, and select a certificate layout with bounded per-module checking. Runtime improvement alone should be credited as completion of prior public certification work. No proof check was performed by this screen.

## Recommendation 2: A109074 corrected factorial-product ratio

- Exact declaration: `OeisA109074.conjecture`.
- Source file: `FormalConjectures/OEIS/109074.lean`.
- Frozen source SHA256: `cd5a2af1993d52ae29df9480d9304cbecae195e24d2ab51a45919806899cfd1e`.
- [Frozen source](https://github.com/google-deepmind/formal-conjectures/blob/a2f4a1bb12a28e04a969da78feefac7d1ce49565/FormalConjectures/OEIS/109074.lean).
- Statement: `∀ n, frac (n+1) = (b (n+1) : ℚ) / (b n : ℚ)`, with `frac n = choose(6n−2,2n)/(2 choose(4n−1,2n))` and `b` the natural-number factorial product for A005156.
- Equivalence/reservation group: **A109074, A005156 and the corresponding A134357 denominator/ratio formulation**. Do not allocate the same product-integrality bridge separately.
- Status: **candidate new formalization of known mathematics**, not a new ASM enumeration or a new mathematical proof.

### Mathematical credit and scope

[OEIS A005156](https://oeis.org/A005156) attributes the enumeration formula to a conjecture of Robbins proved by Kuperberg and records the exact factorial product with Razumov–Stroganov attribution. It links [Kuperberg, Symmetry classes of alternating-sign matrices under one roof](https://arxiv.org/abs/math/0008184) and [Razumov–Stroganov, On refined enumerations of some symmetry classes of alternating sign matrices](https://arxiv.org/abs/math-ph/0312071). The ratio follows from the known product, once integrality and positivity of the natural quotient are available. [A109074](https://oeis.org/A109074) still uses older conjecture wording and cites Bressoud's 1999 book; this is not evidence that the underlying enumeration is newly open.

The frozen `b` is **natural division**, so a proof cannot simply cancel a rational product and ignore truncation. It must establish denominator divisibility and positivity (or a faithful equivalent bridge). This is the major remaining formalization issue and can be substantial. The screen does not establish that the full job is easy. Prefer this to an unsolved global recurrence only if the worker is capable of factorial valuation/integrality arguments.

### Existing-Lean and source-fidelity checks

There are no result directories matching A109074 in the Epoch snapshot and no matching Google/AlphaProof Nexus result file. Bounded web searches for `A109074 Lean`, `A005156 Lean proof`, and `OeisA109074 conjecture` found no completed proof. Live GitHub repository searches for `A109074`, `A005156`, and `oeis 109074` returned zero repositories. Issue/PR searches found historical misformalization reports and [correction PR #5231](https://github.com/google-deepmind/formal-conjectures/pull/5231), not a proof of the corrected statement.

The old `n=1` counterexample and old use of the ternary Fuss–Catalan formula are irrelevant to this frozen source. PR #5231 by `tadamcz` defines `b` by the actual A005156 product and fixes the shift; the source now tests `b 0 = 1`, `b 1 = 1`, `b 2 = 3`, `b 3 = 26`, `b 4 = 646`. Preserve that source and do not claim the old erratum as a disproof.

## Rechecked exclusions and unpromoted alternatives

- **A052709 remains rejected.** Frozen SHA256 `75d87868eacbc17d0b0b1c14751f68be6c8a7347ba095049040c10d6e3fa0794`. Exact target `OeisA52709.conjecture` has one accepted Epoch run: [public Spec.lean](https://github.com/epoch-research/LeanOpenProblems-results/blob/main/runs/oeis-full-50usd-ant-j0j0g4uzligm1k41/oeis_52709_conjecture_0/Submission/Spec.lean). The two other runs score `I`. Its live OEIS citation to the informal Adamczewski proof was not the only exclusion reason after this fresh screen.
- A113019, A358684's main bound, and A001146's forward divisibility fact already contain actual proofs in the frozen repository, even without a `formal_proof` metadata URL. Do not mistake missing metadata for missing Lean.
- A034693 `exists_k_best_possible` likewise already has a complete witness-19 proof. The remaining unassigned `research solved` declarations without a formal-proof URL are not an easy reserve: A111291's eventual refactorable-number bound invokes substantial density/PNT results, and A038552's class-number-one theorem is far beyond the requested short-formalization scope.
- A048153, A049473, A084046, A064169 and A185895 have accepted Epoch result groups and were not promoted.
- A113010's fixed-point question has only finite public evidence excluding further solutions through `10^1000`; it is not a known short proof target. A110835 is Sierpinski's substantial prime-interval conjecture. Neither is an easy replacement.
- A004290 has a known proof of the endpoint formula `a(10^k−1)=repunit(9k)`, but the frozen main theorem additionally claims a strict global record bound. The endpoint proof alone does not settle it; not promoted.

No third distinct sequence group met both a credible known-mathematics route and the bounded absence-of-completed-Lean screen. These two are reviewable leads, not claims of guaranteed easy completion or exhaustive novelty clearance.
