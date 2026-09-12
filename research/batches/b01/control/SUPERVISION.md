# Ongoing supervision of seven Cursor workers

User authorization, September 12, 2026: check every 10 or 15 minutes, keep seven Cursor workers running, and replace completed/already-solved targets with new problems. A prior informal proof without an existing Lean proof is acceptable work. The configured interval is 15 minutes. Automation ID: maintain-seven-cursor-math-workers; heartbeat attached to the coordinating Codex task.

## Authority and accounting

This document records the user's updated policy and supersedes the original worker prompts only on target replacement and known informal proofs. All exact-statement, attribution, axiom, scope and publication requirements continue to apply. Each new worker receives these revised rules explicitly; do not assume existing workers automatically read a later coordinator commit.

Maintain six OEIS slots and one non-OEIS slot. The two Codex workers are separate and their target reservations remain in force. Do not alter unrelated Cursor chats or environment-build agents. Initial campaign URLs are in cursor-launches.json; source/target reservations are in assignments.json. Read both before each check. Save subsequent mappings, predecessor/successor relationships, actual branch names and status changes in supervision-state.json. The coordinator is the sole writer of shared control files. Do not overwrite worker files or uncommitted changes from another task.

A slot is occupied by a running agent, a goal awaiting automatic continuation, or a queued/provisioning launch. A completed transcript does not necessarily mean its goal has stopped; inspect the current goal/run state. Record audit_pending for an unverified claimed result and audit it before replacing that slot. Never start a second active attempt for the same slot or equivalent problem. Before retrying a launch, reconcile the visible existing chat and URL; a slow or failed UI response does not prove creation failed.

A user pause, stop, reduced budget or cancellation is authoritative. Do not restart agents that the user deliberately stopped. Account spending/concurrency limits, provider outages and lost authentication are not reasons to launch replacement storms. Use bounded retries, record the blocker and notify the user if persistent. The target of seven is best effort subject to these conditions and scheduler/browser availability.

## Decision rules

- Healthy worker: inspect substantive progress and current goal, leave it working.
- Unexpectedly stopped, unfinished worker: resume the same chat/branch from its status and handoff. Verify Goal active. Do not restart research from scratch.
- Prior mathematical solution, no matching public Lean proof: send the existing worker the updated authorization to formalize that proof. Record known_mathematics_formalization. Check the proof's validity and fit to the exact formal target before implementation. Credit the mathematical proof's original authors; Wentao Li receives credit only for actual new formal proof development/write-up. Preserve collective formalization and license credit. Record AI assistance. Never describe this as a new mathematical resolution.
- Prior exact public Lean proof: inspect the actual theorem and dependencies sufficiently to establish that it covers the assigned target, record dated public links, retire the target, then fill its slot.
- Claimed new proof/disproof or newly formalized known proof: preserve its commit/artifacts and independently audit it before recording Lean-verified success. An assistant's claim, a green default build of a sorry-based library, a benchmark score, or numerical evidence is insufficient.
- Eight-hour research session exhausted: preserve partial lemmas, failed approaches, counterexamples and handoff; stop the old goal and continuation timers, confirm cessation, mark retired_incomplete, and choose a fresh target for that slot. Do not call exhaustion a solution. New replacement agents receive their own eight-hour session budget. This ongoing replacement campaign has no user-specified end date; continue until the user pauses/cancels it, subject to existing spending limits. Eight-hour deadlines in prompts are worker rules, not new hard platform billing caps.

## Result audit

Fetch the worker branch/commit without merging. Read its source, proof.md, literature audit, exact-type check and verification log. Where practical, compile the actual source in an isolated compatible checkout using the pinned Lean/dependency versions and relevant cached modules. Use only targeted builds. A fresh reviewer/coordinator must confirm the theorem matches the original intended mathematical statement and exact frozen declaration or its full negation. Audit quantifiers, domains, indexing, arithmetic subtraction, rational normalization, answer placeholders, nonvacuity, and all dependencies.

Require final theorem axioms to be a subset of propext, Classical.choice, Quot.sound. No sorryAx, extra axioms, weakened statements, native_decide or Lean.trustCompiler in accepted results. An original imported conjecture or helper with sorry cannot be used as evidence. Experimental disproofs require a kernel-checked exact counterexample. Audit_pending is an honest state when the coordinator cannot yet reproduce/check the result. Do not silently skip verification to keep turnover high.

Keep mathematical_novelty and formalization_novelty as separate fields. Recheck public literature before a novelty claim. No public search can certify universal absence of prior work; report sources checked and remaining uncertainty.

## Replacement protocol

1. Confirm the predecessor is stopped/completed and its relevant timers/goals cannot resume competing work. Do not delete the chat, branch or artifacts.
2. Select a tractable correctly formalized target appropriate to its slot. Either apparently unresolved mathematics or known mathematics lacking an exact public Lean proof qualifies under the updated policy. Prefer an exact result over an already-solved special case. Do not use a specification loophole as a success.
3. Screen original sources, current DeepMind/Epoch/Google results, public Lean repos, papers and discussion sites. Compare declarations and mathematical equivalence, not filenames. Check all active/reserved Cursor and Codex targets and historical exclusions. Previously completed user targets stay excluded unless the new statement is demonstrably different and recorded. Related forms must remain with one owner.
4. Keep the established source baseline for this campaign unless a specific corrected/new target requires a separately documented compatible baseline. Pin source SHA and toolchain in the replacement prompt; never auto-upgrade other workers mid-run. A target absent from the current baseline must not be invented or silently redefined.
5. Assign a unique run ID such as cursor-03-r02 and a unique worker branch/output folder. Update the shared assignment register atomically in a local commit; maintain historical rows and retire previous ownership. Adapt the original checker/schema coherently if needed to distinguish active from historical reservations. Do not simply append duplicate owners and ignore validator failures.
6. Write a complete concrete prompt under control/prompts, including exact target/source hash, scope, revised acceptance policy, deliverables, author credits, original-source links, research strategy and stop conditions. Push the coordinator change to the user fork before launch so the cloud agent can read it.
7. Launch one replacement in the prepared VictorLiwentao/formal-conjectures Cursor environment, from the appropriate coordination seed. Select Grok 4.6 Extra High; do not silently substitute a different model. Each worker uses its own branch and output folder. No duplicate subagents.
8. Use Cursor's /goal command and verify the actual Goal active bar. A submitted/queued command or prose acknowledgement alone is not activation. If goal creation is delayed, inspect for the create-goal event or a reported error and use a bounded corrective follow-up. Preserve the session budget across follow-ups.
9. Record the agent URL, actual branch when available, seed commit, launch/goal verification, target ownership, predecessor and timestamp. No more than seven occupied campaign slots.

## Communication and access

Use the authenticated Cursor UI through cua_repl with fresh state. GitHub access does not by itself grant Cursor control. Browser UI controls and sign-in can become unavailable. Local heartbeat execution depends on the coordinating host and scheduler being available; do not imply a guaranteed 24/7 external service or exact cadence through sleep/outages.

Public pushes to the user's working branches are authorized. Do not submit PRs, edit OEIS, contact authors, add paid services, change spend limits or expand account access. Normal research follow-ups to these agents are authorized. Stay quiet when healthy state is unchanged. Notify the user for verified results, material prior-solution findings, replacements, persistent failures or required action, with concise links and precise result status.

The monitor is ongoing. The original LAUNCH.md sentence saying no monitor exists is historical and is superseded by this document.
