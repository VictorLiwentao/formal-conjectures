# cursor-01-r03 — A051903 question 2

You occupy one of six OEIS slots among seven Cursor workers, with two separately reserved Codex workers. Read control/assignments.json, control/SUPERVISION.md and control/replacement-screening-04.md under research/batches/b01/. Use the prepared VictorLiwentao/formal-conjectures environment and Cursor Grok 4.6 Extra High, from the coordination seed in the launch message. Use your own new branch (preference codex/b01-cursor-01-r03). No subagents or autonomous target switching.

## Exact target

ID: A051903-C2. Source declaration: OeisA51903.conjecture2.
Source: FormalConjectures/OEIS/51903.lean.
SHA-256: 3a694eccc4bd92c14e28e609563bad0ecdfb8895f45c6de887b46fcfcd483db4.
Frozen source baseline: a2f4a1bb12a28e04a969da78feefac7d1ce49565.
Lean: leanprover/lean4:v4.33.1. Preserve lake-manifest.json and dependencies.
Sources: https://oeis.org/A051903 and https://github.com/google-deepmind/formal-conjectures/blob/a2f4a1bb12a28e04a969da78feefac7d1ce49565/FormalConjectures/OEIS/51903.lean .

Question2 asks whether there exists a natural n with Odd n, 1 < a n, and b^n ≡ b^(a n) [MOD n] for EVERY natural b, where a n is the exact existing maximum prime-factor exponent definition. Only question2 is assigned. Question1 is equivalent to the major open Lehmer totient problem and is excluded. Question3 fixes base2 and is different; do not claim to solve it. Reserve the entire A051903 family and equivalent A327295 all-terms-even question to this worker for equivalence checks, without authorizing proof work on C1/C3.

The promising answer is NO. Prove the FULL negation of the RHS existential with the unchanged definitions, then an explicit False ↔ RHS answer theorem. The source uses answer(sorry): do not claim success by exploiting that placeholder or proving a vacuous wrapper. Do not use the original admitted theorem as evidence. Preserve source files; put an explicit answered-type wrapper in your worker directory and audit that its only source-statement change is resolving the answer to False. If the proposed negative route fails, investigate the exact question honestly; do not weaken its all-b quantifier.

Write only research/batches/b01/workers/cursor-01-r03/. Target files: targets/A051903-C2/A051903.lean, proof.md, literature.md, verification.md; worker STATUS.json/HANDOFF.md. Record branch, source hash, UTC kickoff/deadline immediately. No source/config/dependency/shared-control/other-worker edits.

## Initial audit and proposed route

Check live OEIS comments, links and history; all-state DeepMind PRs/issues by filename, A051903, a51903 and equivalent mathematics; Google AlphaProof Nexus and Epoch results; GitHub proof repos/code; papers and discussions about Carmichael lambda, maximum prime-factor exponents and power-map congruences. Inspect actual statement/proof artifacts. An upstream research-open tag or sorry does not establish openness. Record URLs/dates/commits/coverage/inaccessible sources; repeat before final claims. Check OEIS editability if visibly possible, report unknown if not, and never submit an edit.

A known informal proof without completed public exact Lean is explicitly acceptable, with original proof-author credits and classification known_mathematics_formalization. An exact prior public Lean proof must be checked and reported; stop rather than duplicate it. Numerical/benchmark evidence cannot certify either proof or absence. The coordinator's elementary negative route is not a novelty claim. Related prior work: Dutta and Dutta, February2026, https://rxiv.org/pdf/2602.0018v1.pdf , Theorem1 classifies universal power exponents via maximum prime exponent and Carmichael lambda. The screen found no explicit odd/nonexistence corollary or Lean proof there. Inspect its assumptions/proof and credit any actual dependence; it is prudent to frame the result as an elementary corollary/known-mathematics formalization unless a thorough independent novelty audit justifies more. Do not infer correctness from publication alone.

Proposed argument, to validate before Lean:
1. Let e=a n>1 and choose an odd prime p at which the maximum exponent e is attained. Prove this from the actual primeFactorsList/count/foldr max definition, including n≠0 and existence. Obtain p^e∣n and n>e.
2. Apply the universal congruence with b=1+p and reduce modulo p^e.
3. For odd p, the unit 1+p has order p^(e−1) modulo p^e. Alternatively use a proved lifting-the-exponent lemma: v_p((1+p)^n−(1+p)^e)=1+v_p(n−e), with all positivity/nonzero hypotheses. Conclude p^(e−1)∣n−e.
4. Since p^(e−1)∣n too, deduce p^(e−1)∣e. But p≥3 and e≥2 imply p^(e−1)>e, contradicting divisibility of the positive integer e.

Do not assume the order/LTE theorem as an axiom. Inspect Mathlib's existing facts and prove any missing bridge. Natural subtraction needs n>e; establish it. Base1+p (not merely1+p^(e−1)) is required for the full prime-power order. The all-b condition includes this unit without any coprimality assumption in the target. The argument applies to odd n; do not silently generalize it to even n. A formalized maximum-exponent or LTE helper alone is not a solution.

## Execution and stopping

Enable /goal and verify actual Goal active; explicitly call Cursor create-goal if needed. Work productively across turns for up to EIGHT TOTAL HOURS from this replacement kickoff, recording UTC start/deadline. Follow-ups/recreated goals never reset the clock. Respect spending/runtime limits. Change proof approach within this target after prolonged lack of progress; do not idle to consume time.

Stop after a fully self-audited exact answered candidate (coordinator independent audit pending), verified prior exact Lean proof, defective statement, or original time/spending limit. Cancel continuation subscriptions and deactivate the goal so it cannot resume. Known-mathematics formalization meets candidate completion. Do not select a successor or spawn agents; coordinator manages replacements.

Use cached dependencies, targeted module builds and lake env lean. Avoid full lake build, lake clean or lake update. Start LEAN_NUM_THREADS=2; keep commands bounded and preserve logs/process diagnostics. Recover stalls without discarding prior work.

## Acceptance and attribution

Compile proof source with warnings as errors, a separate exact answered-type wrapper, and #print axioms for every final theorem. Allowed closure only propext, Classical.choice, Quot.sound (or fewer). No sorryAx, custom axioms, native_decide, Lean.trustCompiler, altered definitions, weakened quantifiers, unchecked computation or reliance on admitted source helpers. Imported source test lemmas using native computation must not enter the final dependency closure. Prove any needed facts independently if their axioms violate the allowlist.

Preserve Apache notices: Copyright 2026 The Formal Conjectures Authors. Copyright 2026 Wentao Li. Credit original Lean formalization collectively to The Formal Conjectures Authors; mathematical question to Thomas Ordowski (verify current source); actual new independent Lean development/write-up to Wentao Li. Credit prior mathematical/Lean proof authors if found and disclose actual AI assistance. Keep mathematical_novelty separate from formalization_novelty; no priority claim merely because bounded search found nothing.

STATUS.json: exact target, branch, baseline/sourcehash, mathematical/formalization novelty, current status, proof declarations, unresolved gaps, nextstep, UTC timestamps/deadline. HANDOFF.md: reproduction and final commit. proof.md explains maximum attainment, modular/LTE step, contradiction and exact negative answer. literature.md records evidence; verification.md contains commands/type/axiom logs. Partial lemmas, conditional results and numerical tests are not full completion; self-review cannot set independently_verified.

Public pushes only your own branch to https://github.com/VictorLiwentao/formal-conjectures.git. No main/upstream push, PR, OEIS edit, author contact, spending change, new paid service, broader access or other publication. Preserve useful failed work as unverified scratch. Coordinator alone writes shared assignments and accepts/replaces candidates.
