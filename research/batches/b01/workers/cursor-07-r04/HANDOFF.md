# HANDOFF — cursor-07-r04 / WOWII20

Branch: `cursor/b01-cursor-07-r04-9d2b`
Seed: `7a37b78ee539aab88ebbb77a2579f838e9fcc7a6`
Source SHA256: `969908dc9e73fd3ebea73cdf272df476583efbe9745185fd466726c5d4faa2e7`
Kickoff UTC: `2026-09-13T02:53:13Z`
Deadline UTC: `2026-09-13T10:53:13Z` (eight hours, never reset)

Reproduce the candidate (after it compiles):

```sh
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true \
  research/batches/b01/workers/cursor-07-r04/targets/WOWII20/WOWII20.lean
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true \
  research/batches/b01/workers/cursor-07-r04/targets/WOWII20/WOWII20_audit.lean
```

Coordinator independent audit remains. No PR. Push only this worker branch.
