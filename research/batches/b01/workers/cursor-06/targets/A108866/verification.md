# Verification — A108866

Incomplete. No independently verified full proof or disproof.

## Frozen type

See `FormalConjectures/OEIS/108866.lean`:

```
theorem conjecture {n : ℕ} (hn : n > 3) :
    (ratExpression n).num ≡ 0 [ZMOD (n^2 : ℤ)] ↔ n.Prime
```

SHA-256: `afa95297bd177a882fb72b03f32f1da68ecae58d9126981567562462b73266f8`.
Confirmed on the working tree by `sha256sum FormalConjectures/OEIS/108866.lean`.

## Even converse and odd identity (kernel-checked, not the full iff)

Command:

```
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-06/targets/A108866/A108866.lean
```

Re-run after each Lean change. The even lemma `#print axioms` result from the previous checkpoint:

```
'OeisA108866.not_n_sq_dvd_num_of_even' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exact type, from `#print OeisA108866.not_n_sq_dvd_num_of_even`:

```
theorem OeisA108866.not_n_sq_dvd_num_of_even : ∀ {n : ℕ},
  n > 3 → Even n → ¬(OeisA108866.ratExpression n).num ≡ 0 [ZMOD ↑n ^ 2]
```

The odd identity theorems are in the same file. They do not use `OeisA108866.conjecture`. Re-print their axioms after the next compile.

Source module build:

```
LEAN_NUM_THREADS=2 lake --wfail build 'FormalConjectures.OEIS.«108866»'
```

Assignments:

```
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-06
```

PASS.

## Experiments

c5-k4 already scanned `n=4..4000` (do not repeat as novelty). New script: `experiments/scan_beyond_c5k4.py`.
