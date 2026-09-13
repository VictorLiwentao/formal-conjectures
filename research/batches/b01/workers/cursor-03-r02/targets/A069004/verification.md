# Verification log (cursor-03-r02 / A069004)

## Environment

- Seed: `1107856a264a066e316c3cba7b5339be475f6304`
- Frozen source: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
- `sha256sum FormalConjectures/OEIS/69004.lean` = `c29abb2a5c1e48761cc6d7ebb4332bd728071b6ea6059263ffcf153800282ca2`
- `lean-toolchain`: `leanprover/lean4:v4.33.1`
- `LEAN_NUM_THREADS=2`

## Commands

Compile the checker, then independent chunks, then glue:

```bash
export LEAN_NUM_THREADS=2
ROOT=research/batches/b01/workers/cursor-03-r02/targets/A069004
lake env lean -DwarningAsError=true -R "$ROOT" -o "$ROOT/Core.olean" "$ROOT/Core.lean"
python3 "$ROOT/scripts/compile_chunks.py"
lake env lean -DwarningAsError=true -R "$ROOT" -o "$ROOT/GlueCert.olean" "$ROOT/GlueCert.lean"
lake env lean -DwarningAsError=true -R "$ROOT" -o "$ROOT/GlueCount.olean" "$ROOT/GlueCount.lean"
lake env lean -DwarningAsError=true -R "$ROOT" "$ROOT/A069004.lean"
```

Pilot (already succeeded): `Pilot.lean` one Pratt tree, 4s; `C0.lean` 150 certificates, 22s; `CountPilot.lean` `countRange 0 1000 = 168`, 11s.

Separately compiled type audit: `ExactType.lean` (frozen sorry types) then `TypeMatch.lean` (worker theorems inhabit those types).

## Axioms (to be filled after glued compile)

```
#print axioms Cursor03R02.A069004.upper_bound_false
#print axioms Cursor03R02.A069004.conjecture2
```

Required: subset of `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`.

## Formalization audit

See `literature.md`. Types copied from `FormalConjectures/OEIS/69004.lean` after import, not from memory.
