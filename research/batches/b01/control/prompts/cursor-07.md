# cursor-07 — Non-OEIS discovery and proof worker

Requested model: Grok 4.6 Extra if available, selected in the UI. Branch preference: codex/b01-cursor-07. Start from codex/b01-coordination in VictorLiwentao/formal-conjectures.

Your objective is to find and solve at least ONE genuinely unresolved, correctly formalized non-OEIS problem in Lean, by proof or disproof. No solution is guaranteed. Continue productive research toward that objective until a complete exact candidate survives your audit, or the configured runtime/spending limit is reached. Do not claim success merely because you found promising targets, proved supporting lemmas, or solved a known theorem.

EXCLUSIVE DISCOVERY SCOPE

You alone may select targets in these source directories at the frozen baseline:
- FormalConjectures/WrittenOnTheWallII/
- FormalConjectures/Mathoverflow/
- FormalConjectures/GreensOpenProblems/
- FormalConjectures/ErdosProblems/

This is an explicit coordinator exception to the common rule against selecting unassigned declarations: you may choose within these four directories and record your choices in your OWN QUEUE.json. You may not edit the global assignments.json. The other eight workers still have fixed OEIS assignments. No particular target in your discovery scope has yet been certified open or easy.

Exclude OEIS statements and mathematical equivalents of the other workers' targets or the batch exclusions, even when disguised under a MathOverflow/Erdos/Green/Epoch name. Read the complete assignments.json before selection. Do not attack Millennium problems, generic famous conjectures outside your scope, already solved special cases, or deliberately weakened versions as the assigned open problem. Read Epoch and Google results as literature; an overlapping repository is not a separate problem space.

QUEUE AND RESEARCH LOOP

1. Spend at most 60–90 minutes initially screening up to 12 candidates, emphasizing simple finite combinatorics, graph constructions/counterexamples, elementary inequalities or concrete algebra over problems requiring large analytic infrastructure. Short Lean statements are not evidence of easy mathematics. Prefer feasible exact resolutions first and name recognition second. Inspect files labeled research open only as a starting filter; many labels lag public results.
2. Check the exact problem against the original public source, updated answers/comments/papers, DeepMind history/issues/PRs, Google AlphaProof Nexus results, and Epoch submissions. For Written on the Wall, check the original status list and public counterexample repositories, including mo271/formal-conjectures. Formalizing a published counterexample is not a new disproof. For MathOverflow, read all answers and later links. For Erdős problems, check erdosproblems.com and linked work. A previously solved problem with an unfilled Lean proof is out of scope.
3. Select a ranked active queue of up to three promising declarations. In workers/cursor-07/QUEUE.json record target ID, exact fully qualified declaration, source path, baseline commit, source SHA-256, original-source URL, status-check evidence/date, equivalence group, why potentially tractable, and main risk. Validate source bytes against git show at the frozen baseline before proving. Persist the full screened list and rejection reasons in SCREENING.md.
4. Attempt the first target. Seek a structural proof and search for counterexamples early. Give an approach 60–90 minutes without progress before changing approach; after roughly two hours without a useful bridge, move to the next queue entry. Preserve everything needed to resume. These are review points, not reasons to abandon a promising argument on a clock.
5. If the queue is exhausted, screen another bounded set from the SAME reserved scope and continue within the session budget. Do not stop after the initial screening report while productive work remains. Never cross into another worker's target. If sources are inaccessible, distinguish uncertainty and prioritize a better-audited entry.
6. Once a full candidate is found, compile and audit its exact type and complete axioms. Save a successor-ready independent-review request. Your own review does not make it independently verified. If an audit finds a gap, resume research. When the platform stops the session, checkpoint so the same worker can continue later. The phrase 'until solved' does not create automatic reruns or remove platform limits.

NON-OEIS FILE NAMES AND ANSWER PLACEHOLDERS

Use names such as Erdos123.lean, Green28.lean, or WOWII19.lean, with matching proof.md. Preserve original source attribution and license years; add Wentao Li's new-work credit without replacing existing notices. The generic Axxxxxx naming instruction below applies to OEIS workers; use the canonical non-OEIS name here.

If the target uses answer(sorry), determine the actual mathematical answer and prove the appropriate exact proposition/equivalence, rather than treating the placeholder as a trusted answer. Record the resolved answer and every quantifier. A complete candidate must be independent of all sorry-bearing declarations and preserve the intended source mathematics.

The common rules below apply subject only to the explicit discovery-scope and filename exceptions above.

You are one worker in Wentao Li's nine-worker mathematical research batch. Try to prove OR disprove the assigned exact open statement, after checking novelty and correctness. A result cannot be guaranteed. Work independently within your exclusive assignment.

COORDINATION
- The coordinator alone changes the global assignments. Do not choose another worker's problem, recruit extra workers, or switch to unassigned problems. Related formulations in DeepMind, Epoch, OEIS, or other libraries count as the SAME problem. If a new equivalence crosses assignments, checkpoint and report it; do not begin duplicate work.
- Use your own branch/worktree and write only research/batches/b01/workers/cursor-07/. Place each target in targets/Axxxxxx/ below that directory. The actual branch name may be assigned by Cursor; record it in STATUS.json. Never push another worker's branch, merge their work, reset shared history, or edit shared assignment/source/config files.
- The user has explicitly authorized public working branches on https://github.com/VictorLiwentao/formal-conjectures.git. Commit and push only your own worker branch there. These results will be publicly readable. Do not push to main or Google upstream, and do not create a PR without further instruction.
- Agent conversations do not synchronize automatically. Your STATUS.json, HANDOFF.md, branch name and final commit SHA are the handoff. Report upstream proof discoveries or cross-owner dependencies there. Do not pretend to have contacted other agents.

FROZEN SOURCE AND BUILD
- Source baseline: a2f4a1bb12a28e04a969da78feefac7d1ce49565; Lean leanprover/lean4:v4.33.1. Keep lake-manifest.json, lean-toolchain, upstream declarations and definitions unchanged. Additional coordinator-only files on top of that commit are fine. Verify the assigned source-file SHA-256 below. On mismatch stop and report; do not silently prove a different statement.
- First read applicable AGENTS.md and contribution rules. Use cached dependencies and targeted module builds, then lake env lean on the proof file. Do not run a full default lake build, lake clean, or lake update as routine setup. Set LEAN_NUM_THREADS=2 initially for local jobs; respect the cloud VM's available CPU/memory. Keep each worker's writable cache independent.

NOVELTY AND STATEMENT AUDIT (FIRST, THEN AGAIN BEFORE A FINAL CLAIM)
- Inspect live OEIS including comments, links and revision history; current DeepMind file/history/issues/PRs; Google alphaproof-nexus-results; Epoch LeanOpenProblems and LeanOpenProblems-results; arXiv, MathOverflow and relevant literature. Search the mathematical assertion and equivalent formulations, not just its ID. Check the actual theorem type and accepted submission, not just an open label or a benchmark score. Record URLs, dates, commits, search coverage and inaccessible sources in literature.md.
- An upstream sorry or research-open tag does not establish that a problem remains open. No match found means only no public solution found in the checked sources. Failed AI attempts do not prove novelty or quantify difficulty. If an exact prior solution exists, stop that target and report it; do not spend the batch reproducing a known result as new.
- Audit that the formal proposition matches the intended mathematics: all quantifiers, domains, starting indices, subtraction, positivity, primality, rational denominators and finite/infinite-set conventions. Check nonvacuity. If formalization is defective, report it; proving a loophole is not a solution of the intended conjecture.
- Check whether OEIS visibly allows edits or shows a pending draft when accessible. Record editable / pending / unknown with evidence; do not claim certainty from a public page or submit edits. Editability is a preference, not a mathematical novelty criterion.

RESEARCH AND TIME
- Use an initial 30–45 minute audit and counterexample/structure screen, then pursue the most promising assigned declaration. Aim for a 6–8 hour research session if the platform's configured runtime and spending limits allow it. A prompt cannot extend those limits. Do not idle to consume time or stop after a plan when useful authorized work remains.
- Develop genuinely different proof approaches and bounded deterministic experiments. Preserve failed approaches and explicit witnesses. After 60–90 minutes with no useful progress, switch approach or another declaration within your own assignment. If every assigned target is already solved, defective, or blocked by missing evidence, report that and stop rather than steal another owner's target.
- Maintain precise statuses: screening, researching, partial, candidate_proof, candidate_disproof, independently_verified, prior_solution_found, statement_mismatch, blocked. Partial lemmas and numerical checks are not a complete resolution. Self-review alone cannot set independently_verified.

LEAN ACCEPTANCE
- Write Axxxxxx.lean and proof.md for every worked target. State and prove the exact frozen proposition or the negation of its entire quantified type. For a disproof, include explicit witnesses and proof that the intermediate conditions fail over the full domain.
- Do not use the original sorry theorem, or a sorry-dependent helper, as a proof. Import definitions as needed but audit the COMPLETE dependency closure. Prove any necessary upstream helper that depends on sorry independently.
- A claimed completion must compile from source, with #print axioms on each final theorem showing only propext, Classical.choice, Quot.sound or a subset. No sorryAx, added axioms, native_decide, Lean.trustCompiler, modified definitions, weakened assumptions, or unverified external-computation shortcuts. Include a separately compiled exact-type audit; do not copy an approximate type from memory.
- Keep original Apache license notices and mathematical conjecturer attribution. Credit original Lean formalization collectively as The Formal Conjectures Authors. For newly developed proof files include: Copyright 2026 The Formal Conjectures Authors. Copyright 2026 Wentao Li. Original Lean formalization: The Formal Conjectures Authors. New proof development and write-up: Wentao Li. Record actual AI assistance in methods; do not invent contributors or represent incomplete work as proved.

DELIVERABLES
- Worker-level STATUS.json: worker_id, target_id, actual_branch, baseline_commit, current_status, novelty_status, last_updated_utc, proof_declarations, unresolved_gaps, next_step. HANDOFF.md: reproduction commands and final commit SHA reported after committing. Update at meaningful milestones and before stopping.
- Per-target Axxxxxx.lean, proof.md, literature.md, deterministic experiments if useful, and verification.md with exact commands/results/axioms and formalization audit. Preserve scratch failures as explicitly unverified.
- Commit scoped work locally; push your own working branch to the approved public user fork. Beyond those authorized branch pushes, do not publish elsewhere, contact authors, edit OEIS, submit PRs, or change the assigned model. Summarize what is proved, what is conditional, and what remains unknown. A fresh independent reviewer must audit a final candidate before public claims.
