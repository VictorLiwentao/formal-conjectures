# Verification — WOWII7

Toolchain: `leanprover/lean4:v4.33.1`
Baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
Source SHA256: `b24ee6ea69c547654647cdad7102ce95e64dc8a455fbd9aa12f7214b3d3c3968`
Worker branch: `cursor/b01-cursor-07-r05-e27b`
Candidate SHA256: `c85feea04b8babc79e8fd9a5c227f74ed725534edaa101a63f7e4d0ef1e3244c`

## Commands

```sh
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true \
  research/batches/b01/workers/cursor-07-r05/targets/WOWII7/WOWII7.lean
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true \
  research/batches/b01/workers/cursor-07-r05/targets/WOWII7/WOWII7_audit.lean
```

No full `lake build`, `lake clean`, or `lake update`.

## Axioms

`#print axioms WOWII7.conjecture7` reports

```
[propext, Classical.choice, Quot.sound]
```

No `sorryAx`, extra axioms, `native_decide`, or `Lean.trustCompiler`.

## Exact type

Pretty-printed type of `WOWII7.conjecture7`:

```
{α : Type u_1} [Fintype α] [DecidableEq α] [Nontrivial α]
  (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
  have maxL := (image (fun v => G.indepNeighborsCard v) univ).max' ⋯;
  ↑↑maxL - 1 + ↑↑(Fintype.card α) - 2 * ↑↑G.indepNum ≤ G.Ls
```

This matches the frozen declaration
`WrittenOnTheWallII.GraphConjecture7.conjecture7`
except the source theorem remains `sorry`. Integer subtraction is on `ℤ`
before the real cast. `Ls` is unchanged.

The audit file imports the frozen source only to `#check`/`#print` that type.
Self-review does not mark independent verification.
