# HANDOFF — cursor-02 / A108081

Worker branch: `cursor/b01-cursor-02-13c0`
Baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
Coordination: `238f78bdd5701ae4c97a0d70d4e22e2d45770d7a`
Kickoff UTC: 2026-09-12T23:10Z. Session budget: eight hours from kickoff (until 2026-09-13T07:10Z). This follow-up does not restart that budget.

Final commit SHA: `8ac1cb22b1cdcdcf85d3b5f808e87addeab964a9`.

## Reproduction

```bash
sha256sum FormalConjectures/OEIS/108081.lean
# b03761724c1052d613a676584301d6ad1f3d20aff62aa421525ef8b6b611a54d
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-02
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-02 --against 238f78bdd5701ae4c97a0d70d4e22e2d45770d7a
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/enumerate_structure.py
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/decomposition.py
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/bijection_search.py
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/catalan_peels.py
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/pword_signs.py
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/pword_catalan_split.py
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/right_pword_factor.py
python3 research/batches/b01/workers/cursor-02/targets/A108081/experiments/xia_concat_split.py
LEAN_NUM_THREADS=2 lake --wfail env lean research/batches/b01/workers/cursor-02/targets/A108081/A108081.lean
```

## Status

`partial`. No public exact proof/disproof found. Finite counts through `n=14` are already public (c5-k4) and are not a resolution. Statement uses `a(n-1)`, matching Xia’s listed cardinalities `1,2,7`, not the OEIS prose `a(n+1)`.

Lean now proves `|Right_n| = C_{n-1}`, `|P_n| = C_n`, and `|Y_n| = H_{n-1}`. The I×Y rebuild bijection, `|I_n|`, and the quantified Xia identity remain open.
