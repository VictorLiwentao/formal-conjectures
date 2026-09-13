# cursor-07-r05 — WOWII7 strengthened Griggs spanning-tree leaf bound

You occupy the single non-OEIS slot in a seven-worker Cursor campaign, alongside six OEIS slots and two independently reserved Codex workers. Read research/batches/b01/control/assignments.json, SUPERVISION.md and replacement-screening-07.md before work. Follow the coordination seed in the launch message. Prepared VictorLiwentao/formal-conjectures environment, Cursor Grok 4.6 Extra High. Own new branch (preference codex/b01-cursor-07-r05) and research/batches/b01/workers/cursor-07-r05/ only. No subagents or autonomous target switches.

## Exact source and target

Target ID WOWII7; declaration WrittenOnTheWallII.GraphConjecture7.conjecture7.
Source FormalConjectures/WrittenOnTheWallII/GraphConjecture7.lean.
SHA256 b24ee6ea69c547654647cdad7102ce95e64dc8a455fbd9aa12f7214b3d3c3968.
Frozen baseline a2f4a1bb12a28e04a969da78feefac7d1ce49565; Lean leanprover/lean4:v4.33.1. Do not upgrade dependencies or edit source/config.

For every finite nontrivial vertex type and simple connected graph G, prove Ls(G) ≥ n + μ − 2α − 1, where α=G.indepNum and μ=max_v indepNeighborsCard G v. Match the exact frozen declaration:

```lean
theorem conjecture7 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    ((maxL : ℤ) - 1 + (Fintype.card α : ℤ) - 2 * (G.indepNum : ℤ) : ℝ) ≤ Ls G := by
  sorry
```

The displayed sorry identifies the source target; no admitted proof may survive in your candidate. Keep all finite-type/typeclass/connectedness assumptions. The left side uses integer subtraction before casting to real, not truncated natural subtraction. Ls is a real supremum over spanning subgraphs whose coercions are trees; leaves have subgraph degree exactly one. Establish boundedness and an actual spanning-tree witness. Do not replace Ls with maximum degree, induced-tree order, or leaves of a nonspanning tree. Only this exact theorem is assigned.

All non-OEIS prefixes remain reserved to this slot, but do not work on other targets. WOWII31, WOWII101, WOWII20 and Green66 plus equivalent A001481/A256435/Erdos222 gap bounds are completed/excluded. Reserve the strengthened Griggs/Graffiti leaf bound and equivalent connected domination bound with this single owner. The original paper calls this Conjecture 2; do not confuse it with WOWII2, which already has public Lean proofs.

Write targets/WOWII7/WOWII7.lean, proof.md, literature.md and verification.md; worker STATUS.json and HANDOFF.md. Preserve source Apache notice and its collective 2026 copyright. In new proof files include Copyright 2026 The Formal Conjectures Authors. Copyright 2026 Wentao Li. Credit original Lean statement collectively; prior mathematical authors accurately; Wentao Li for actual new Lean proof development/write-up; disclose AI assistance.

## Literature and mathematical route

This is known mathematics. It is acceptable to formalize a known proof without a located exact public Lean proof. Do not claim a new mathematical discovery. Independently inspect the original Written on the Wall II question/source and the coordinator screen. Recheck all-state DeepMind PRs/issues, Epoch and AlphaProof Nexus, public Lean repos and mathematically equivalent strengthened Griggs/connected-domination bounds. A stronger existing Lean theorem that directly implies the target counts as prior coverage even under another name. If exact public Lean is found, verify its proof/dependencies and stop with a cited report; coordinator selects replacement. Record bounded search evidence and inaccessible sources; absence is not universal priority certification.

Primary mathematical source: Ermelinda DeLaVina, Siemion Fajtlowicz and Bill Waller, On Some Conjectures of Griggs and Graffiti (March 2002, revised May 2003), https://www.uhd.edu/documents/academics/sciences/griggsngraffiti.pdf . Read Conjecture 2 and Lemma 1 on printed pp. 2, 4–5. Seed a connected set with a maximum independent neighborhood and its center. Augment by one independent vertex and at most one connector until domination. The invariant |T|≤2|M|−μ+1 gives |T|≤2α−μ+1; attaching remaining vertices as leaves finishes. Validate connectivity, independence, termination and small cases; the screen provides details.

The proof route is a proposal until checked in Lean. Finite-set maximality may be simpler than implementing the paper's iterative sequence. A connected dominating set need only give a spanning tree with AT LEAST n−|T| leaves; do not assume its complement is exactly the leaf set for arbitrary small graphs. Verify the μ≤1 / complete-graph and n=2 corners explicitly. The weaker Griggs bound Ls≥n−2α+1 does not settle the assigned μ>2 cases.

Inspect FormalConjecturesForMathlib/Combinatorics/SimpleGraph/SpanningTree.lean for Ls and local independence/connected-domination APIs. Public AlphaProof Nexus WOWII2 contains potentially useful spanning-tree lemmas but proves a different average-neighborhood bound. Public c5-k4 WOWII183 has connected-domination certificate infrastructure in limited cases. Neither was found to supply this universal strengthened result in the coordinator screen. If reusing public Lean, inspect actual types/dependencies and license, cite immutable sources and authors, and distinguish reused code from Wentao Li's work. If a sufficient general theorem is found, stop for prior-proof reconciliation. Do not assume historical Lemma 1, connected domination estimates, or any original source sorry as an axiom.

## Persistent execution and stopping

Enable /goal and verify Goal active (call create-goal if necessary). Record actual branch, source hash, UTC kickoff and deadline immediately. Work productively across turns for up to EIGHT TOTAL HOURS from this replacement kickoff. Follow-ups and recreated goals never reset that clock. Existing runtime/spending limits remain authoritative. Change approach within this target after prolonged lack of progress; do not idle to use time.

Stop after a fully self-audited exact candidate pending coordinator independent audit, a verified prior exact public Lean proof, a defective source, or the original time/spending limit. Cancel continuation timers and deactivate the goal so it cannot resume. Preserve compiled partial results and explicit unresolved gaps at timeout. No successor selection or extra agents. Partial domination lemmas, conditional bounds or finite tests are not the exact target.

Use cached dependencies and targeted modules via lake env lean; avoid full lake build, lake clean or lake update. Start LEAN_NUM_THREADS=2, bound long commands, log errors and process status. Preserve work through failures.

## Acceptance and publication

Compile candidate source with warnings as errors and a separate exact-type wrapper against the frozen declaration; print axioms for every final result. Allowed closure only propext, Classical.choice, Quot.sound, or a subset. No sorryAx, custom axioms, native_decide, Lean.trustCompiler, weakened definitions or original conjecture admissions. A green default repository build is not verification.

STATUS.json records exact target, branch, source baseline/hash, mathematical/formalization novelty separately, proof declarations, unresolved gaps, next step and UTC clocks. HANDOFF provides reproduction and final commit. proof.md explains the complete mathematical chain and corners. literature.md records source dates/URLs and prior-author credit; verification.md records exact type, commands and axiom logs. Self-review cannot mark independently_verified.

Public push only your own worker branch to https://github.com/VictorLiwentao/formal-conjectures.git. No main/upstream push, PR, OEIS edit, author contact, shared control edits, spending-limit changes, broader access or new paid services. Coordinator alone accepts results and manages replacement ownership.
