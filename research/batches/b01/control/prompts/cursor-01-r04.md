# cursor-01-r04 — A001818 permanent identity, C1 only

You occupy one of six OEIS slots among seven Cursor workers and two separately reserved Codex workers. Read research/batches/b01/control/assignments.json, SUPERVISION.md and replacement-screening-06.md first. Use the launch-message coordination seed, prepared VictorLiwentao/formal-conjectures environment and Cursor Grok 4.6 Extra High. Own new branch (preference codex/b01-cursor-01-r04) and research/batches/b01/workers/cursor-01-r04/ only. No subagents, shared-control writes or autonomous target switching.

## Exact target and frozen source

ID A001818-C1, OeisA1818.conjecture1.
Source FormalConjectures/OEIS/1818.lean, SHA256 1e41db84e11a5adb981526a75330a597a13ceef8479eb4fb4ef832256496dffe.
Baseline a2f4a1bb12a28e04a969da78feefac7d1ce49565. Lean leanprover/lean4:v4.33.1. Source and dependency versions stay unchanged.

For every n≥1 and primitive complex 2n-th root ζ, prove the permanent of the 2n by 2n matrix with diagonal1 and off-diagonal (1+ζ^(i-j))/(1-ζ^(i-j)) equals (product k<n of (2k+1))². Preserve exact Fin indexing, integer negative exponents, complex division, root order and natural-to-complex cast. Check source elaboration explicitly: differences must have the intended integer type, not truncated natural subtraction. The zero-based indexing differs from the paper's1-based labels only by a simultaneous shift, leaving differences unchanged. Establish all required denominator nonvanishing and root-power distinctness.

Only C1 is assigned. Same-owner related groups A001818, A002454 and A356041 are reserved to prevent duplicate attempts on the odd-size companion and shared general permanent identity. C2 modulo p² is not assigned; do not start it if C1 finishes. Proving a helper or an odd-size variant alone does not solve this target.

Write targets/A001818-C1/A001818.lean, proof.md, literature.md, verification.md and worker STATUS.json/HANDOFF.md. Original-source URL https://github.com/google-deepmind/formal-conjectures/blob/a2f4a1bb12a28e04a969da78feefac7d1ce49565/FormalConjectures/OEIS/1818.lean and https://oeis.org/A001818 . Stop if prompt absent or pinned hash differs.

## Prior work and proposed strategy

Known mathematics, not a new mathematical discovery. Yue-Feng She, Zhi-Wei Sun and Wei Xia, A novel permanent identity with applications, arXiv:2208.12167v2, Theorem1.3(ii), prove this statement. Read the whole dependency chain and §5 proof, https://arxiv.org/html/2208.12167v2 and https://arxiv.org/pdf/2208.12167 . The even-size result is C1; the odd-size companion covers A002454. Their general rational-function identity links the Cayley-kernel permanent to a perfect-matching sum and to a determinant. The proof of Thm1.3 specializes to roots of unity, using determinant/eigenvalue identities; inspect which path best fits Lean's existing Matrix.permanent, determinant, permutation, polynomial and IsPrimitiveRoot APIs. Formalizing this machinery is likely substantial: no promise of a short proof. Use the known argument to choose a coherent route rather than repeatedly checking small n.

Section5 also depends on the Guo–Li–Tao–Wei derangement identity (Lemma5.2), arXiv:2206.02592, https://arxiv.org/abs/2206.02592 . Read and formally prove any required dependency; the coordinator screen outlines this route.

Before implementing, audit the mathematical proof, signs, diagonal shift, even dimension, conjugation/transposition and all zero denominators. A permanent is not a determinant and a circulant permanent cannot be replaced by a product of eigenvalues without a proved special identity. No assuming a cited identity or theorem as an axiom. Prove any missing general lemma in your worker folder. An alternative shorter exact proof is welcome, but track every dependency.

Fresh coordinator screening found PR5568 changes references/status only and leaves both source proofs admitted. All three Epoch C1 attempts fail with sorryAx; C2 attempts also fail (Google changes a definition). Inspect actual public attempts for useful partial lemmas with proper credit. A failed benchmark or sorry in source does not establish absence of public proof. Search all-state DeepMind PRs/issues, Epoch, AlphaProof Nexus, public Lean repositories and equivalent She–Sun–Xia/Cayley-kernel/permanent identities, including A002454/A356041. If a correct stronger public Lean theorem implies C1, record its coverage and stop rather than duplicate. Recheck before final claims. Report sources/date/URL/commit/limitations. Check visible OEIS editability if possible; report unknown rather than infer, and never submit an edit.

A prior informal proof without public exact Lean remains acceptable; classify known_mathematics_formalization. Preserve mathematical authors' credits and the collective original formalization attribution. Include Copyright 2026 The Formal Conjectures Authors. Copyright 2026 Wentao Li. Credit Wentao Li for actual new Lean development/write-up and disclose Cursor AI assistance; preserve Apache notices. No first-formalization or mathematical priority claim from bounded search absence.

## Execution and stopping

Use /goal, call create-goal if necessary and verify actual Goal active. Record branch, UTC kickoff and eight-hour deadline immediately. Work productively across continuations for up to EIGHT TOTAL HOURS from this replacement kickoff; follow-ups/recreated goals do not reset the clock. Existing spending/runtime limits remain authoritative. Change approach within C1 after prolonged lack of progress, preserving useful partial lemmas and failed approaches. Do not idle to consume time.

Stop after a fully self-audited exact candidate pending independent coordinator audit, verified prior exact public Lean, defective source, or original time/spending limit. Cancel timers and deactivate the goal on stop. Incomplete partial lemmas are not a solution. Do not select a successor, spawn agents or work on C2. Coordinator manages acceptance and replacement.

Use cached dependencies and targeted lake env lean module builds. Avoid full lake build, lake clean, lake update or toolchain changes. Start LEAN_NUM_THREADS=2 and bound/log long commands. Preserve progress through compile failures.

## Exact acceptance and deliverables

Compile candidate with warnings as errors and a separate exact-type wrapper against the frozen statement. Print all final theorem axioms. Allowed transitive closure only propext, Classical.choice, Quot.sound or a subset. No sorryAx, extra axioms, native_decide, Lean.trustCompiler, unchecked computation, weaker quantifiers, redefined a or matrices, or use of the original admitted conjecture/helper. A successful default source build is not a proof.

STATUS.json records exact target, source hash/baseline, actual branch, mathematical/formalization novelty separately, proof declarations, unresolved gaps, nextstep and UTC clocks. proof.md explains the full informal proof chain and edge cases; literature.md documents prior work and credits; verification.md records exact types, commands and axioms; HANDOFF.md provides reproduction and final commit. Self-review cannot mark independently_verified.

Public push only your own worker branch to https://github.com/VictorLiwentao/formal-conjectures.git. No main/upstream push, PR, OEIS edit, author message, broader access, spending-limit change, paid service or other publication. Write only your worker directory; coordinator alone edits shared control files.
