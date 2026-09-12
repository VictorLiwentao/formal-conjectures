# cursor-05 — Ordinary and unitary divisor sums

Requested model: Grok 4.6 Extra (select in UI if available; no substitution). Select this in the platform UI; text alone does not set a model.
Branch preference: codex/b01-cursor-05.

Your exclusive targets:
- A063880: OeisA63880.mod_216_of_a, OeisA63880.unique_primitive_108
  Source: FormalConjectures/OEIS/63880.lean
  SHA-256: b50d00e13735613cbe37bd3a25c19130874e8f036ca2a0e3c1aceb177a33c683
  Reference: https://oeis.org/A063880

Approach and known caveats: Begin with mod_216_of_a; unique_primitive_108 is a stronger secondary target. The primitive decomposition is already known and must not be claimed as new. Public c5-k4 work already searched powerful cores extensively; pursue local valuations or structural constraints instead of repeating that search.

Other workers' reserved groups (do not work on these): cursor-01: A237271; cursor-02: A108081; cursor-03: A076141; cursor-04: A135508; cursor-06: A108866, A332786, A330718; codex-01: A079727; codex-02: A003161, A003162.

Global exclusions (do not restart): A280246, A098275-C1, A220119-C1, A397588, A361033, A368634, A368629, A368626, A368628, A375439, A368633-C1, A368635, A000139, A007226, A060957, A022030, A052709, A181546, A176477, A103885, A103425, A357513, A067857, A007406, A141057, A211417, A109074.

You are one worker in Wentao Li's eight-worker mathematical research batch. Try to prove OR disprove the assigned exact open statement, after checking novelty and correctness. A result cannot be guaranteed. Work independently within your exclusive assignment.

COORDINATION
- The coordinator alone changes the global assignments. Do not choose another worker's problem, recruit extra workers, or switch to unassigned problems. Related formulations in DeepMind, Epoch, OEIS, or other libraries count as the SAME problem. If a new equivalence crosses assignments, checkpoint and report it; do not begin duplicate work.
- Use your own branch/worktree and write only research/batches/b01/workers/cursor-05/. Place each target in targets/Axxxxxx/ below that directory. The actual branch name may be assigned by Cursor; record it in STATUS.json. Never push another worker's branch, merge their work, reset shared history, or edit shared assignment/source/config files.
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
