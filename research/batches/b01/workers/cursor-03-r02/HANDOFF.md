# HANDOFF — cursor-03-r02 / A069004

## Clock

- Start UTC: `2026-09-13T00:13:02Z`
- Deadline UTC: `2026-09-13T08:13:02Z` (eight hours from kickoff; follow-ups do not restart)
- Branch: `cursor/b01-cursor-03-r02-4f64`
- Seed: `codex/b01-coordination` at `1107856a264a066e316c3cba7b5339be475f6304`
- Frozen source: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
- Source SHA-256: `c29abb2a5c1e48761cc6d7ebb4332bd728071b6ea6059263ffcf153800282ca2` (matches)

## Exclusive target

`OeisA69004.conjecture2.variants.upper_bound_false` and same-group corollary `OeisA69004.conjecture2`.
Do not work A076141 or any other assignment.

## Reproduction

From the repository root:

```bash
export LEAN_NUM_THREADS=2
ROOT=research/batches/b01/workers/cursor-03-r02/targets/A069004
mkdir -p "$ROOT/lean"
lake env lean -DwarningAsError=true -R "$ROOT" -o "$ROOT/lean/Core.olean" "$ROOT/Core.lean"
python3 "$ROOT/scripts/compile_chunks.py"
lake env lean -DwarningAsError=true -R "$ROOT" -o "$ROOT/lean/GlueCert.olean" "$ROOT/GlueCert.lean"
lake env lean -DwarningAsError=true -R "$ROOT" -o "$ROOT/lean/GlueCount.olean" "$ROOT/GlueCount.lean"
lake env lean -DwarningAsError=true -R "$ROOT" "$ROOT/A069004.lean"
lake env lean -DwarningAsError=true -R "$ROOT" "$ROOT/ExactType.lean"
lake env lean -DwarningAsError=true -R "$ROOT" "$ROOT/TypeMatch.lean"
```

## Final commit SHA

`b142c424` (sources + olean-path fix + glue script). Independent chunk compile is running; glue not yet kernel-checked.

## Notes

Inspected Epoch Anthropic / OpenAI / Google `oeis_a069004_conjecture_2` submissions (all score I).
Anthropic has a complete-looking Pratt database and prime-count chain with `decide +kernel` and no `native_decide`.
Repair: replace `powModAux e` fuel with fuel 64 before compiling chunks.
GlueCert uses one `okChunks_cons` lemma per chunk rather than a single nested term.
