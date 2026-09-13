# cursor-07-r02 — WOWII101 independence-core inequality

You occupy the single non-OEIS slot among seven Cursor workers and two separately reserved Codex workers. Read control/assignments.json, control/SUPERVISION.md, and control/replacement-screening-02.md under research/batches/b01/. Use the prepared VictorLiwentao/formal-conjectures Cursor environment and Cursor Grok 4.6 Extra High. Start at the coordination seed named in the launch message, on your own new worker branch (preference codex/b01-cursor-07-r02). Do not run subagents.

## Exact exclusive target

- ID: WOWII101; Hajnal independence-core inequality.
- Frozen declaration: WrittenOnTheWallII.GraphConjecture101.conjecture101.
- Source: FormalConjectures/WrittenOnTheWallII/GraphConjecture101.lean.
- SHA-256: 870cd77d2cb8bf98fcbe4bdeee7c52620009af97368fc4358dc595af716046c6.
- Source baseline: a2f4a1bb12a28e04a969da78feefac7d1ce49565.
- Toolchain: leanprover/lean4:v4.33.1; preserve pinned lake-manifest.json.
- Target: for a finite nontrivial connected simple graph G, G.indepNum ≤ (Fintype.card α + (alphaCore G).card) / 2, with the exact existing alphaCore defined by a strict drop in independence number after vertex deletion.
- Source URL: https://github.com/google-deepmind/formal-conjectures/blob/a2f4a1bb12a28e04a969da78feefac7d1ce49565/FormalConjectures/WrittenOnTheWallII/GraphConjecture101.lean

Write only research/batches/b01/workers/cursor-07-r02/. Target outputs: targets/WOWII101/WOWII101.lean, proof.md, literature.md, verification.md. Worker-level STATUS.json and HANDOFF.md are required. Record actual branch, source hash, UTC kickoff and deadline immediately. Do not modify upstream source, shared control files, toolchain, dependencies or other workers' files.

This is KNOWN MATHEMATICS, already marked research solved in the source. The acceptable aim is a new Lean implementation when no completed exact public Lean proof is located, not a new mathematical discovery. Credit Hajnal and the actual expository proof sources you use. The predecessor WOWII31 was independently compiled but an earlier public exact Lean proof by Kenta Kitamura/KitaKen1 was found through DeepMind PR4658. Do not repeat WOWII31 or imply that an upstream sorry means no public proof exists. WOWII133 screening is preserved with the retired worker and is not your assigned target.

## First audit and proof strategy

Verify the source SHA, exact quantified type and definitions, including natural-number division, the induced graph after vertex deletion, and independence-number semantics. Prove that the deletion-based alphaCore equals the intersection of all maximum independent vertex sets. This is essential to matching Hajnal's formulation; do not replace the definition without a proved equivalence.

Read Levit–Mandrescu https://arxiv.org/pdf/1101.4564, especially Corollary 2.4, and check Hajnal attribution. The original statement PR is https://github.com/google-deepmind/formal-conjectures/pull/3820.

A promising elementary route is the finite-family inequality |intersection F| + |union F| ≥ 2α for any nonempty family F of maximum independent sets. Start with one maximum set. On adding another maximum set S, let I and U be the previous intersection and union. I ∪ (S ∩ U) is independent: every vertex of I coexists with each vertex of U in some previous maximum independent set. Its cardinality is at most α=|S|; deduce |I \ S| ≤ |S \ U|. Thus intersection loss is at most union gain, preserving the bound. For all maximum sets, |union| ≤ |V| and the core equivalence yield 2α ≤ |V|+|core|, then the exact floor-division conclusion. Confirm every set/cardinality step before formalizing. Existence of maximum independent sets and induced-graph transport are the likely Lean work. A stronger disconnected-graph lemma is allowed only if it really implies the exact assigned theorem.

Before substantial work, and again before a final novelty statement, search current DeepMind file/history and ALL open/closed issues/PRs; Google AlphaProof Nexus, Epoch LeanOpenProblems/results; GitHub repositories/code; original mathematical sources and equivalent theorem names (Hajnal lemma, core/corona, intersection/union of maximum independent sets). Search actual proof artifacts, not only benchmark scores. The bounded coordinator screen located no exact public completed Lean proof; that is not proof of universal absence. Inspect existing Mathlib facts too. Report URLs, dates, commit hashes, inaccessible sources and actual coverage. A valid prior informal proof is allowed. An earlier exact public Lean proof must be checked against the full frozen type and dependency closure, recorded and reported; stop rather than duplicate it. Failed or resource-limited public scripts must be inspected and credited.

## Research, duration and stopping

Use /goal and explicitly register the objective with Cursor's create-goal capability if necessary; verify it is active. Productively pursue the exact target across turns for up to EIGHT TOTAL HOURS from this new run's first kickoff. Record UTC start/deadline. Follow-ups and recreated goals do not restart the clock. Respect account/runtime/spending limits. Do not idle to consume time. After 60–90 minutes without useful progress, change proof approach within this target. Do not switch to other targets, choose your own successor, create extra agents or acquire paid services.

Stop after a complete self-audited exact candidate (coordinator review remains pending), a verified prior exact public Lean proof, a defective statement, or the original eight-hour/spending limit. On stopping cancel continuation subscriptions and deactivate the goal so it cannot resume, preserving handoff. Known-mathematics formalization IS an acceptable candidate; do not continue searching for novel mathematics because of older prompt wording. The coordinator handles audit and replacement. Never label a self-reviewed candidate independently_verified. Report partial/conditional/unverified work honestly.

## Lean verification and credits

Use cached dependencies and targeted module builds plus lake env lean. Avoid full lake build, lake clean and lake update. Start LEAN_NUM_THREADS=2 and keep long commands bounded, with logs and process status so stalled jobs can be recovered. Keep writable caches local to this worker.

A final result must prove the exact frozen proposition or its entire negation. Do not use the source sorry theorem or sorry-dependent helpers. Imports of definitions require full dependency auditing. Compile actual proof source with warnings treated as errors, separately compile an exact-type comparison to the frozen declaration, and print axioms of every final theorem. Allowed axioms only propext, Classical.choice, Quot.sound (or fewer). No sorryAx, extra axioms, native_decide, Lean.trustCompiler, weakened assumptions, changed definitions or unverified external certificates. Numerical checks and partial lemmas are not complete proofs. Save reproduction commands and logs in verification.md.

Preserve Apache license and include: Copyright 2026 The Formal Conjectures Authors. Copyright 2026 Wentao Li. Original Lean formalization: The Formal Conjectures Authors. New independent Lean development/write-up: Wentao Li. Attribute original mathematical proof and any reused prior Lean code to their actual authors. Disclose actual AI assistance in methods. Do not claim priority or new mathematics.

Commit and push only your own public working branch to https://github.com/VictorLiwentao/formal-conjectures.git. No main/upstream push, PR, author contact, OEIS edit, spend-limit change or other publication. STATUS.json records worker_id, target_id, actual_branch, baseline/source hashes, current_status, mathematical_novelty, formalization_novelty, proof_declarations, unresolved_gaps, next_step, UTC timestamp and deadline. HANDOFF.md records reproduction and final commit SHA. The coordinator alone reserves targets and manages replacements; all active/reserved/retired mathematical equivalents in assignments.json are excluded.
