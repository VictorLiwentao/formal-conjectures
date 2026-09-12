# Start the nine agents later

Nothing launches automatically from the repository files. Markdown instructions alone do not activate Cursor goal mode. Use /goal and verify the visible Goal active bar; a queued or submitted command is not yet confirmation. You do not need to paste the long prompts: after choosing the correct starting branch, paste a short instruction that tells the agent to read its prompt file.

## Cursor: seven separate Cloud agents

Use VictorLiwentao/formal-conjectures and starting branch codex/b01-coordination. Reuse the prepared environment if it is available for this repository. Select the requested model in the UI, set an appropriate spending/runtime limit, and disable automatic PR creation if that option is offered. Each agent must get a separate worker branch.

For Cursor 1 paste:

```text
/goal You are cursor-01. Read research/batches/b01/control/prompts/cursor-01.md and research/batches/b01/control/assignments.json, then execute your assignment. Work on your own branch. If either file is missing, stop and report the wrong starting branch.
```

Repeat in six new Cloud agents, replacing BOTH occurrences of cursor-01 with cursor-02, cursor-03, cursor-04, cursor-05, cursor-06, and cursor-07 respectively. The last one is the non-OEIS worker. Do not send all seven IDs to a single agent and assume that launches seven agents.

## Codex: two separate local worktrees

Open this fork as a project and start two tasks in separate worktrees based on codex/b01-coordination. Select Astra high/xhigh as desired. Use the same short instruction with codex-01 and codex-02 respectively. Do not start in the existing A060957 worktree.

## Continue an unfinished worker

Resume that SAME agent/task and its existing branch. Paste:

```text
Continue your existing assignment from STATUS.json, QUEUE.json if present, and HANDOFF.md. Preserve previous results and exclusions. Refresh current public-solution checks before a substantial new attempt. Keep working within your assigned scope and configured session budget; checkpoint if the platform stops you. Do not restart from scratch or claim an automatic future run.
```

## Control and reports

The current connection can read GitHub branches, but no authenticated Cursor API connection is configured here. Cursor offers an API for launching agents, reading status, sending subsequent runs and canceling runs. A user API key can enable a future local controller; put it in a local secret store/environment rather than chat or Git. Browser UI control is another possible route if the user signs in and authorizes the actions. Neither route is configured or activated by this document.

Preassigned ownership remains useful with either API or browser control. Send the coordinator the launched agent URLs/branch names and Codex task names to collect reports on demand. No background monitor or automatic rerun has been scheduled.

Sources: https://cursor.com/docs/cloud-agent and https://cursor.com/docs/cloud-agent/api/endpoints

## Goal-mode verification

For an existing Cursor worker, use the /goal slash command in its follow-up composer, keep its original assignment and eight-hour total research budget, and submit the follow-up (a running agent may first queue it). Verify that the UI shows **Goal active** above the composer. A create-goal tool event is additional confirmation. Keep the same agent and branch. The requested eight-hour deadline is an agent instruction, not a newly configured hard platform spending cap. Goal mode does not guarantee a mathematical resolution or uninterrupted provider availability.

Official source: https://cursor.com/changelog/08-19-26
