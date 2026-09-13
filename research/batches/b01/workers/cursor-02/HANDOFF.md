# HANDOFF — cursor-02 / A108081

Worker branch: `cursor/b01-cursor-02-13c0`
Baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
Coordination: `238f78bdd5701ae4c97a0d70d4e22e2d45770d7a`
Kickoff UTC: 2026-09-12T23:10Z. Session budget: eight hours from kickoff (until 2026-09-13T07:10Z). This follow-up does not restart that budget.

Final commit SHA: `c7708f336b27d9229412d39a061bb956b2e6c1ce`.

## Reproduction

```bash
sha256sum FormalConjectures/OEIS/108081.lean
# b03761724c1052d613a676584301d6ad1f3d20aff62aa421525ef8b6b611a54d
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-02
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-02 --against 238f78bdd5701ae4c97a0d70d4e22e2d45770d7a
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/enumerate_structure.py
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/decomposition.py
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/iword_left_factors.py
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/left_prefix_any_xia.py
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/gword_dropLast.py
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/cons_zero_converse.py
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/pword_concat_one_xia_prefixes.py
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/rightword_bad_remainder.py
LEAN_NUM_THREADS=2 lake --wfail env lean research/batches/b01/workers/cursor-02/targets/A108081/A108081.lean
```

## Status

`partial`. Session budget ended at 2026-09-13T07:10Z without an exact proof or disproof. No public exact proof/disproof found. Finite counts through `n=14` are already public (c5-k4) and are not a resolution. Statement uses `a(n-1)`, matching Xia’s listed cardinalities `1,2,7`, not the OEIS prose `a(n+1)`. Formalization is not defective.

Lean proves `|Right_n| = C_{n-1}`, `|P_n| = C_n`, `|Y_n| = H_{n-1}`, unique I×Y rebuild `|X_n| = ∑_k |I_k| H_{n-k}`, unique shortest left `PWord` factor of I-words, `|Left_n| = C_{n-1}`, `|Z_n| = H_{n-1}`, `C_{n-1} ≤ |I_n| ≤ H_{n-1}`, prefix cancellation for `L(Left)` and for `L(s ++ [1])` with last-`1` `PWord` `s`, closure `L(Left)++I ⊆ I` and `L(s ++ [1]) ++ I ⊆ I` for every `PWord s`, the Callan lower bound, and the matching converse: last-`1` unique-zero words with penultimate at least `2` never glue to an I-word. Hence `|I_n|` equals the Callan recurrence `q(1)=1`, `q(k)=2 C_{k-1}` for `k≥2`.

This checkpoint also proves the Cauchy rewrite `|I_{n+1}| + |I_n| = 2 ∑_{k=0}^{n-1} C_k |I_{n-k}|` for `n ≥ 1`, and `(H * C)_n = 2 H_n` for `n ≥ 1`. The remaining gap is the algebraic identity `∑_k |I_k| H(n-k) = a(n-1)` against Lean’s Fibonacci-binomial `a`. Continuation timers for this session are not armed.
