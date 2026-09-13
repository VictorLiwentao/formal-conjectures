# cursor-07-r03 — Green66 known quarter-power bound

You occupy the single non-OEIS slot among seven Cursor workers and two separately reserved Codex workers. Read control/assignments.json, control/SUPERVISION.md and control/replacement-screening-03.md under research/batches/b01/. Use Cursor Grok 4.6 Extra High in the prepared VictorLiwentao/formal-conjectures environment, from the coordination seed in the launch message. Create your own new branch (preference codex/b01-cursor-07-r03). No subagents or autonomous target switching.

## Exact target and classification

Target ID: Green66-trivial-bound.
Declaration: Green66.green_66.variants.trivial_bound.
Source: FormalConjectures/GreensOpenProblems/66.lean.
SHA-256: d38ab7e233260302ef58121037a02dc94866ddae820e9fc84308ce7264e07acb.
Frozen source baseline: a2f4a1bb12a28e04a969da78feefac7d1ce49565.
Lean: leanprover/lean4:v4.33.1; preserve manifest/dependency pins.
Source: https://github.com/google-deepmind/formal-conjectures/blob/a2f4a1bb12a28e04a969da78feefac7d1ce49565/FormalConjectures/GreensOpenProblems/66.lean
Primary exposition: Ben Green, A list of open problems, problem66, https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf .

Prove exactly: there exists a positive real constant C such that, for all sufficiently large REAL X, there is a NATURAL n=a²+b² in [X−C X^(1/4), X]. Preserve the existing IsSumOfTwoSquares definition, natural witnesses and real rpow exponent. This is the separate research-solved variant already present in the source.

This is KNOWN MATHEMATICS, a formalization task. It does NOT settle Green's open question with the fixed constant 1/10, and it must never be titled or reported as solving Green problem66. Only the named big-O variant is assigned. Do not prove the answer(sorry) wrapper, modify the constant/domain in the target, or confuse this with the stronger open declaration. All equivalent fourth-root sum-of-two-squares gap statements belong to this worker, including Erdos222 and OEIS A001481/A256435 formulations of this bound. Related LeanGenius code uses an extra axiom and an Epoch OEIS275409 lemma proves a weaker sqrt bound; inspect them as prior work, not accepted exact proofs (see screening notes). All other active/retired targets, including WOWII31 and WOWII101, are excluded.

Write only research/batches/b01/workers/cursor-07-r03/. Required target outputs in targets/Green66-trivial-bound/: Green66.lean, proof.md, literature.md, verification.md. Worker-level STATUS.json and HANDOFF.md are required. Record actual branch, source hash, UTC kickoff and deadline immediately. Do not edit source statements, shared control files, dependencies/toolchain or other worker files.

## Initial audit and proof route

First verify the source hash, prompt and seed. Audit the quantifier order (ONE constant for every sufficiently large real X), positive constant, eventual filter atTop, interval endpoints, natural-square witnesses, and real fourth power. Check the informal bound really matches these definitions and all small/negative-X edge cases are handled by the explicit eventual threshold.

Use Green's two successive greatest-square construction. For large X≥1, let u=floor(sqrt X), residual R=X−u²≥0, then v=floor(sqrt R), and n=u²+v². Prove n≤X and bound the remaining residual by a constant times X^(1/4). A generous explicit C such as10 is sufficient: no optimal constant is requested. Establish floor/nonnegativity bounds, R≤3 sqrt X, and X−n≤2 sqrt R+1, then bridge sqrt(sqrt X) to real rpow X^(1/4) with all positivity hypotheses. This route is a strategy, not a Lean proof; inspect existing Mathlib facts rather than relying on guessed APIs. Connected graph machinery is irrelevant. Keep experiments deterministic if useful, but inequalities and eventual quantifiers require proof.

Before substantial work and again before final claims, search live DeepMind file/history and ALL open/closed issues/PRs by path/stem/declaration and mathematical phrases. Check Google AlphaProof Nexus, Epoch LeanOpenProblems/results, GitHub repos/code, relevant Mathlib lemmas and original literature for equivalent sums-of-two-squares gap/greedy approximation formalizations. The coordinator found no exact public completed Lean proof in bounded screening; this is not a global absence guarantee. An upstream sorry or research-solved tag is not evidence of missing public proof. Inspect exact artifacts and full theorem types, not only scores. Record URLs, dates, commits, coverage and inaccessible sources.

Known informal proof is explicitly allowed: credit the original mathematical source and any actual original authors identified; Green is an exposition source, not automatically the discoverer. If an exact earlier public Lean proof is found and verifies, record it and stop instead of duplicating it. Inspect and credit public failed/resource-limited scripts before reuse. Do not describe an existing Lean lemma applied to the target as a first formalization without careful equivalence checking.

## Execution and stop conditions

Enable /goal, use Cursor create-goal if needed, and verify Goal active. Pursue productive exact-target work across turns for up to EIGHT TOTAL HOURS from this new run's initial kickoff. Record UTC start/deadline. Follow-ups and recreated goals do not reset this clock. Respect account/runtime/spending limits. Do not idle to consume time. Change proof approach after prolonged lack of progress, within this target only.

Stop after a fully self-audited exact candidate (coordinator independent audit still pending), an independently checked prior exact public Lean proof, a defective formal statement, or the original time/spending limit. Cancel subscriptions and deactivate the goal before ending so it cannot resume competing work. Known-mathematics formalization satisfies the candidate stop condition. Do not choose a successor; the coordinator owns reservation and replacement. No new paid services, spending changes, PRs or extra workers.

Use cached dependencies and targeted module builds plus lake env lean. Avoid full lake build, lake clean and lake update. Start LEAN_NUM_THREADS=2. Keep commands bounded, preserve logs and process status, and recover stalled tools without discarding previous work.

## Acceptance, attribution and deliverables

Compile actual proof source with warnings as errors. Separately compile an exact-type check against the frozen target, and print axioms for all final declarations. Final axiom closure must be a subset of propext, Classical.choice, Quot.sound. No sorryAx, new axioms, native_decide, Lean.trustCompiler, weakened statements, changed definitions or unverified computation shortcuts. Never use the original sorry theorem or admitted helper as evidence; imports of definitions still require full dependency checking. Keep partial, conditional, numerical and heuristic results distinct from the completed target. Self-review cannot set independently_verified.

Preserve Apache license and include Copyright 2026 The Formal Conjectures Authors. Copyright 2026 Wentao Li. Credit original Lean statement to The Formal Conjectures Authors, actual independent new Lean development/write-up to Wentao Li, and mathematical argument/any reused Lean code to actual prior authors. Disclose AI assistance in methods. No new-mathematics, priority, optimal-constant or open-Green66 resolution claim.

STATUS.json: worker_id, target_id, actual_branch, baseline/source hashes, status, mathematical_novelty, formalization_novelty, proof_declarations, unresolved_gaps, next_step, UTC timestamp and deadline. HANDOFF.md: reproduction commands and final commit SHA. proof.md explains every inequality and final quantified statement; literature.md preserves sources; verification.md includes exact build/type/axiom logs. Preserve useful failed approaches as unverified scratch.

Commit and push only your own public working branch to https://github.com/VictorLiwentao/formal-conjectures.git. Do not push main/upstream, create PRs, contact authors, edit OEIS, expand access, change spend limits or publish elsewhere. The coordinator alone edits global assignments and handles independent acceptance/replacements.
