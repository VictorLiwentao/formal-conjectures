# Nine-worker research batch b01

Prepared 2026-09-12 for Wentao Li. These are exclusive provisional research leads, not a certification of open status or an estimate of success probability. No research agents have been launched by creating this bundle. The ninth worker has a reserved discovery scope rather than a pre-screened exact target.

| Worker | Exclusive assignment | Initial focus |
| --- | --- | --- |
| Cursor 01 | A237271, corrected Carmichael observation only | Divisor-block lower bound |
| Cursor 02 | A108081 | Recursive word enumeration |
| Cursor 03 | A076141 | Binary substring multiplicity |
| Cursor 04 | A135508 | LCM recurrence at primes |
| Cursor 05 | A063880, both open assertions | Residue mod 216 before primitive uniqueness |
| Cursor 06 | A108866; reserve A332786/A330718 equivalents | Rational-sum primality criterion |
| Cursor 07 | Non-OEIS discovery: Written on the Wall II, MathOverflow, Green and Erdős | Screen a short queue, then try until one exact resolution or the session limit |
| Codex 01 | A079727, all four conjectures | C1/C2 before stronger congruences |
| Codex 02 | A003161 and A003162 | Related supercongruences together |

Start all workers from `codex/b01-coordination` in `VictorLiwentao/formal-conjectures`, recording the exact seed commit. The upstream source is pinned to `a2f4a1bb12a28e04a969da78feefac7d1ce49565`, Lean 4.33.1. Do not automatically synchronize or upgrade dependencies mid-batch. Before another batch, the coordinator reviews upstream changes and the target register.

## Launch

1. In Cursor Cloud, select this fork and the coordination branch as the starting ref. Launch seven separate agents, each with the corresponding full file from `prompts/cursor-01.md` through `cursor-07.md`. Select Grok 4.6 Extra if offered; requested model availability has not been verified. A prompt alone does not select a model. Each cloud agent must use its own branch. Disable automatic PR creation if available.
2. For Codex, open the fork as a project and create two separate worktrees from the coordination branch. Paste `prompts/codex-01.md` and `codex-02.md`, selecting Astra xhigh (or the user's chosen high setting). Two local workers should initially use two Lean threads each. Do not copy or share a writable `.lake` directory from an active worker.
3. Keep a platform spending limit and runtime limit. The requested 6–8 hour research session is a prompt instruction, not a guarantee of platform continuation. No automatic schedules, external calls, or research agents are launched by this bundle.
4. Run the guard before and after work, replacing `<seed-commit>` with the coordination seed SHA:

```sh
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-01
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-01 --against <seed-commit>
```

## Coordination and communication

`assignments.json` is written by one coordinator. Workers never race to claim targets in a shared file. Each owns `research/batches/b01/workers/<worker-id>/`, commits there, and pushes only its own branch. User authorized public working branches on September 12; these are publicly visible. No upstream PRs or OEIS edits are authorized.

The prompts themselves contain all fixed reservations and the non-OEIS discovery scope. They do not require workers to see unmerged sibling branches to avoid the same assigned target. Known equivalent statements are grouped with one owner. The checker enforces unique IDs and declarations, but neither it nor any prompt can guarantee that an undiscovered mathematical equivalence will never cause overlap.

Each worker records STATUS.json and HANDOFF.md. For a progress check, give the coordinator the seven Cursor agent URLs or branch names and the two Codex task names. The coordinator can fetch branch reports without merging; live Cursor transcripts/control require authenticated Cursor access. There is currently no automatic live bridge or scheduler installed. Workers must not claim otherwise.

Only the coordinator reassigns a target, after the previous owner has stopped and handed it off. A worker finding a public proof retires that target instead of selecting from the whole library. A later reviewer can intentionally audit another worker's candidate; that is recorded as a review, not a competing solve attempt. Merge reviewed changes serially. Keep incomplete or rejected candidates clearly marked.

## Screening evidence and limits

Two read-only screens checked the frozen statements, live OEIS, bounded online searches, and local snapshots of Google AlphaProof Nexus results and Epoch results. The details and remaining audit requirements are embedded in each prompt. No matching accepted result was located for the exact assigned assertions in those checks. This is not exhaustive literature clearance; every worker repeats the exact-target audit before investing heavily and before a novelty claim.

A237271 deserves special care: other declarations have accepted public proofs, and an older Carmichael formulation was vacuous. This batch assigns only the corrected `observation_carmichael`. A108081 needs the documented indexing correction checked. A135508 needs its linked thesis inspected. A003161/A003162 have prior partial work. A108866 and the supercongruences may be difficult despite short statements. No defensible numerical solve probabilities are available.

A060957 is excluded because a local exact disproof and independent review already exist; this bundle does not publish that proof. Several other former open labels were excluded after public solutions or specification issues surfaced. See assignments.json. DeepMind and Epoch are overlapping sources, so the batch is partitioned by mathematical target rather than by source repository. The ninth worker now has a separate non-OEIS discovery scope. It must perform comparable exact-target screening before research; no famous problem is presumed tractable merely to fill that slot.

Sources:
- https://github.com/google-deepmind/formal-conjectures
- https://github.com/google-deepmind/alphaproof-nexus-results
- https://github.com/epoch-research/LeanOpenProblems
- https://github.com/epoch-research/LeanOpenProblems-results
- https://github.com/google-deepmind/formal-conjectures/issues/4974
- https://github.com/google-deepmind/formal-conjectures/pull/4987
- https://github.com/Kuberwastaken/c5-k4
- https://cursor.com/docs/cloud-agent
- https://cursor.com/docs/cloud-agent/api/endpoints

Model/API availability and billing should be checked in the actual launch UI. No subscription price or unlimited-use assumption is made here.
