# A108081 verification

Checked 2026-09-13.

## Frozen source

```
sha256sum FormalConjectures/OEIS/108081.lean
b03761724c1052d613a676584301d6ad1f3d20aff62aa421525ef8b6b611a54d
```

Matches `research/batches/b01/control/assignments.json` and the prompt.
Baseline commit: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
Coordination: `238f78bdd5701ae4c97a0d70d4e22e2d45770d7a`.

## Formalization audit

The frozen type is

```
∀ n, n ≥ 1 → Set.ncard (xN n) = a (n - 1)
```

- `a` uses Lean `Nat` subtraction in `(n+k-1).choose k`. For `n=0` this is `0.choose 0 * fib 1 = 1`, matching OEIS `a(0)=1`.
- Tests `a_0`–`a_4` match OEIS `1,2,7,25,92`.
- The OEIS Xia comment asks whether `|X_n| = a(n+1)` for `n ≤ 12`. The listed words of lengths `1,2,3` have cardinalities `1,2,7 = a(0),a(1),a(2) = a(n-1)`. Lean follows the examples, not the prose offset. This is an indexing correction, not a defective statement.
- The OEIS length-3 line `1,-1,0 = L(0),-1,0` is a sign typo for `(-1,-1,0) = L([0]) ++ (-1,0)`. The constructors do not produce `(1,-1,0)`.
- Nonvacuity: `xN 1 = {[0]}`, `a 0 = 1`. Proved in `ncard_xN_one`.
- `Set.ncard` of an infinite set is `0`. Finiteness of `xN n` is proved (`xN_finite`), so the count is not vacuously zero.

Editability of OEIS: unknown. JSON has no draft field; HTML edit/history pages were blocked or 404 without login.

## Commands

```
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-02
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-02 --against 238f78bdd5701ae4c97a0d70d4e22e2d45770d7a
LEAN_NUM_THREADS=2 lake --wfail env lean research/batches/b01/workers/cursor-02/targets/A108081/A108081.lean
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/enumerate_structure.py
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/decomposition.py
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/bijection_search.py
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/catalan_peels.py
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/pword_signs.py
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/pword_catalan_split.py
```

Guard: PASS (worker path only). Source SHA-256 matches.

## Lean axioms

`lake --wfail env lean` on `A108081.lean` succeeded on 2026-09-13.

```
#print axioms ncard_xN_one
-- [propext, Classical.choice, Quot.sound]
#print axioms ncard_xN_two
-- [propext, Classical.choice, Quot.sound]
#print axioms ncard_xN_three
-- [propext, Classical.choice, Quot.sound]
#print axioms exists_shortest_right_parse
-- [propext, Classical.choice, Quot.sound]
#print axioms XWord.convex
-- [propext, Classical.choice, Quot.sound]
#print axioms PWord.not_isAppend
-- [propext, Quot.sound]
#print axioms PWord.of_step_right
-- [propext, Quot.sound]
#print axioms XWord.pword_sign
-- [propext, Classical.choice, Quot.sound]
#print axioms PWord.eq_of_isRightParse_cons_zero_r
-- [propext, Classical.choice, Quot.sound]
#print axioms PWord.take_idxOf_concat_zero
-- [propext, Classical.choice, Quot.sound]
#print axioms PWord.yWord_of_head_eq_zero
-- [propext, Quot.sound]
#print axioms xN_finite
-- [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, `native_decide`, or `Lean.trustCompiler`. The original sorry theorem is imported for definitions only and is not used.

## Exact-type audit of the unproved target

The repository declaration remains `sorry`. This worker file does not restate it as proved. Small cases proved here:

- `(xN 1).ncard = a 0`
- `(xN 2).ncard = a 1`
- `(xN 3).ncard = a 2`

These are not the quantified statement.

## Novelty (repeat before any completion claim)

See `literature.md`. No public exact proof or disproof was found on 2026-09-13. Fried arXiv:2607.24832 treats A108080, not A108081. Do not claim completion.
