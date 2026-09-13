# Verification log (cursor-03-r02 / A069004)

## Environment

- Seed: `1107856a264a066e316c3cba7b5339be475f6304`
- Frozen source: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
- `sha256sum FormalConjectures/OEIS/69004.lean` = `c29abb2a5c1e48761cc6d7ebb4332bd728071b6ea6059263ffcf153800282ca2`
- `lean-toolchain`: `leanprover/lean4:v4.33.1`
- `LEAN_NUM_THREADS=2`
- Session: start `2026-09-13T00:13:02Z`, deadline `2026-09-13T08:13:02Z`
- Glue compile finished `2026-09-13T02:29:36Z`

## Commands

```bash
export LEAN_NUM_THREADS=2
ROOT=research/batches/b01/workers/cursor-03-r02/targets/A069004
mkdir -p "$ROOT/lean"
lake env lean -DwarningAsError=true -R "$ROOT" -o "$ROOT/lean/Core.olean" "$ROOT/Core.lean"
python3 "$ROOT/scripts/compile_chunks.py"
python3 "$ROOT/scripts/compile_glue.py"
lake env lean -DwarningAsError=true -R "$ROOT" "$ROOT/ExactType.lean"
```

`lean -R "$ROOT"` looks up imports in `$ROOT/lean`. Count* blocks were compiled serially (`JOBS=1`) after two concurrent Count jobs each used several GiB.

## Chunk compile

- 284/284 Pratt chunks `C0`–`C283`: `decide +kernel` OK
- 26/26 count blocks `Count000`–`Count500`: `decide +kernel` OK
- `compile.log` ends with `fails 0`

## Glue compile (`2026-09-13T02:29:36Z`)

```
GlueCert.lean exit=0
GlueCount.lean exit=0
A069004.lean exit=0
TypeMatch.lean exit=0
```

## Axioms

```
'Cursor03R02.A069004.upper_bound_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cursor03R02.A069004.conjecture2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Subset of `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`. Worker Lean files contain no `sorry`, `native_decide`, or `trustCompiler`.

## Formalization audit

`ExactType.lean` (frozen sorry theorems) and `TypeMatch.lean` (worker theorems) both compiled. Types copied from `FormalConjectures/OEIS/69004.lean` after import:

- `¬ ∀ n, 1 < n → Nat.primeCounting n ≥ OeisA69004.a n`
- negation of the full `conjecture2` conjunction

`Nat.primeCounting 512720 = 42493` via `Nat.count` of primes in `[0, 512721)`. Witness list length 42494, strictly increasing `s ∈ [1, 512720)`, each `512720²+s²` prime by Pratt/Lucas. That is enough for `42494 ≤ a 512720` and `π(n) < a n`. The remaining 172 reported primes in `a(n)=42666` are unused. Minimality is not claimed.

Not independently verified: a coordinator/reviewer must still reproduce this compile. Status is `candidate_proof`.
