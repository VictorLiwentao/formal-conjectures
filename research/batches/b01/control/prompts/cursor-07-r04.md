# cursor-07-r04 — WOWII20 induced bipartite subgraph bound

You occupy the single non-OEIS slot in a seven-worker Cursor campaign, alongside six OEIS slots and two independently reserved Codex workers. Read research/batches/b01/control/assignments.json, SUPERVISION.md and replacement-screening-05.md before work. Follow the coordination seed in the launch message. Prepared VictorLiwentao/formal-conjectures environment, Cursor Grok 4.6 Extra High. Own new branch (preference codex/b01-cursor-07-r04) and research/batches/b01/workers/cursor-07-r04/ only. No subagents or autonomous target switches.

## Exact source and target

Target ID WOWII20; declaration WrittenOnTheWallII.GraphConjecture20.conjecture20.
Source FormalConjectures/WrittenOnTheWallII/GraphConjecture20.lean.
SHA256 969908dc9e73fd3ebea73cdf272df476583efbe9745185fd466726c5d4faa2e7.
Frozen baseline a2f4a1bb12a28e04a969da78feefac7d1ce49565; Lean leanprover/lean4:v4.33.1. Do not upgrade dependencies or edit source/config.

For every finite nontrivial vertex type and simple connected graph G, prove n/floor(d_avg) ≤ b(G), with the exact real average degree, integer floor cast to real, and b(G) defined by the largest induced bipartite subgraph size. Keep every domain, typeclass, quantifier and connectedness assumption as written. b is a real cast of a natural sSup over vertex subsets; establish boundedness and actual witnesses when using it. No redefining bipartite, replacing floor by ceiling, weakening the graph family, using admitted source helpers, or counting numerical cases as proof. Only this theorem is assigned. All non-OEIS prefixes remain reserved to this slot, but do not work on other targets. WOWII31, WOWII101, Green66 and equivalent A001481/A256435/Erdos222 gap bounds are completed/excluded.

Write targets/WOWII20/WOWII20.lean, proof.md, literature.md and verification.md; worker STATUS.json and HANDOFF.md. Preserve source Apache notice including its original 2025 collective copyright. In new proof files also include Copyright 2026 The Formal Conjectures Authors. Copyright 2026 Wentao Li. Credit original Lean statement collectively; prior mathematical authors accurately; Wentao Li for actual new Lean proof development/write-up; disclose AI assistance.

## Literature and mathematical route

This is known mathematics. It is acceptable to formalize a known proof without a located exact public Lean proof. Do not claim a new mathematical discovery. Independently inspect the original Written on the Wall II question/source and the coordinator screen. Recheck all-state DeepMind PRs/issues, Epoch and AlphaProof Nexus, public Lean repos and mathematically equivalent induced-forest/degenerate-subgraph bounds. A stronger existing Lean theorem that directly implies the target counts as prior coverage even under another name. If exact public Lean is found, verify its proof/dependencies and stop with a cited report; coordinator selects replacement. Record bounded search evidence and inaccessible sources; absence is not universal priority certification.

Primary route: N. Alon, J. Kahn and P. D. Seymour, Large induced degenerate subgraphs, Graphs and Combinatorics 3 (1987), 203–211. Read Theorem1.3/Corollary1.4 and proof, https://web.math.princeton.edu/~nalon/PDFS/Publications/Large%20induced%20degenerate%20subgraphs%20in%20graphs.pdf . A finite graph has an induced forest of size at least Σ_v min(1,2/(deg(v)+1)). Their deterministic induction may be easier to formalize than averaging permutations: remove a vertex of degree at most1 and reinsert it into the induced forest; otherwise remove a vertex of maximum degree and show the weight sum does not decrease. Validate every weight inequality and degree-change case rather than assuming the bound.

For connected nontrivial graphs every degree is at least1; the min disappears. Cauchy–Schwarz gives Σ_v 2/(deg(v)+1) ≥ 2n/(d_avg+1). If d_avg≥2, prove d_avg+1≤2*floor(d_avg), hence the desired n/floor(d_avg) bound. For d_avg<2, connectedness and edge count force a tree, so the whole graph is bipartite; verify floor/denominator positivity separately using d_avg≥1. These are proposed proof steps until formalized. Alternatively establish the exact bound by another valid argument. Forest implies two-colorability needs a proved bridge.

Inspect existing graph APIs, particularly FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Induced.lean: induced coloring equivalence, finite powerset maximum and b definition. Audit dependency closures of every non-Mathlib helper; if any needed source lemma is admitted, prove it independently. Do not assume the AKS theorem or any graph inequality as an axiom.

## Persistent execution and stopping

Enable /goal and verify Goal active (call create-goal if necessary). Record actual branch, source hash, UTC kickoff and deadline immediately. Work productively across turns for up to EIGHT TOTAL HOURS from this replacement kickoff. Follow-ups and recreated goals never reset that clock. Existing runtime/spending limits remain authoritative. Change approach within this target after prolonged lack of progress; do not idle to use time.

Stop after a fully self-audited exact candidate pending coordinator independent audit, a verified prior exact public Lean proof, a defective source, or the original time/spending limit. Cancel continuation timers and deactivate the goal so it cannot resume. Preserve compiled partial results and explicit unresolved gaps at timeout. No successor selection or extra agents. Partial forest lemmas, conditional bounds or finite tests are not the exact target.

Use cached dependencies and targeted modules via lake env lean; avoid full lake build, lake clean or lake update. Start LEAN_NUM_THREADS=2, bound long commands, log errors and process status. Preserve work through failures.

## Acceptance and publication

Compile candidate source with warnings as errors and a separate exact-type wrapper against the frozen declaration; print axioms for every final result. Allowed closure only propext, Classical.choice, Quot.sound, or a subset. No sorryAx, custom axioms, native_decide, Lean.trustCompiler, weakened definitions or original conjecture admissions. A green default repository build is not verification.

STATUS.json records exact target, branch, source baseline/hash, mathematical/formalization novelty separately, proof declarations, unresolved gaps, next step and UTC clocks. HANDOFF provides reproduction and final commit. proof.md explains the complete mathematical chain and corners. literature.md records source dates/URLs and prior-author credit; verification.md records exact type, commands and axiom logs. Self-review cannot mark independently_verified.

Public push only your own worker branch to https://github.com/VictorLiwentao/formal-conjectures.git. No main/upstream push, PR, OEIS edit, author contact, shared control edits, spending-limit changes, broader access or new paid services. Coordinator alone accepts results and manages replacement ownership.
