# Literature — A001818-C1 / `cursor-01-r04`

Screened 2026-09-13 UTC. Bounded public search; later or unindexed proofs may exist.

## Frozen source

- File `FormalConjectures/OEIS/1818.lean`
- SHA256 `1e41db84e11a5adb981526a75330a597a13ceef8479eb4fb4ef832256496dffe`
- Baseline `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
- Declaration `OeisA1818.conjecture1`
- Original URL https://github.com/google-deepmind/formal-conjectures/blob/a2f4a1bb12a28e04a969da78feefac7d1ce49565/FormalConjectures/OEIS/1818.lean
- OEIS https://oeis.org/A001818
- Elaboration check: `(i.val - j.val : ℤ)` is integer subtraction (`= (i.val : ℤ) - (j.val : ℤ)`), not truncated `ℕ` subtraction. Confirmed by `#eval` of `(0 - 1 : Fin 3)` as `ℤ` giving `-1`.

## Mathematics (not new)

1. Yue-Feng She, Zhi-Wei Sun, Wei Xia, *A novel permanent identity with applications*, arXiv:2208.12167v2, 15 September 2022, Theorem 1.3(ii) even case. https://arxiv.org/abs/2208.12167 . Paper `n` is the matrix size. Lean `n` is half-size: paper `n = 2n_Lean`. Then `per = ((2n-1)!!)^2 = a n`.
2. Xuejun Guo, Xin Li, Zhengyu Tao, Tao Wei, *The eigenvectors-eigenvalues identity and Sun’s conjectures on determinants and permanents*, arXiv:2206.02592, Conjecture 1.1(1) / even derangement identity used as She–Sun–Xia Lemma 5.2(i). https://arxiv.org/abs/2206.02592
3. F. Calogero, A. M. Perelomov, *Some diophantine relations involving circular functions of rational angles*, Linear Algebra Appl. 25 (1979), 91–94. Eigenvalues of the Hermitian cotangent circulant.
4. Zhi-Wei Sun, MathOverflow 427232, 24 July 2022, with later confirmation. https://mathoverflow.net/questions/427232
5. Han Wang, Zhi-Wei Sun, arXiv:2206.02589, companion determinant identities (not the C1 permanent).

C2 (Yang–Zhang arXiv:2605.19502 Prop. 17) and A002454 (odd-size companion of Thm 1.3(ii)) are **not assigned**.

## Public Lean screening (2026-09-13)

- DeepMind PR5568, merged `acbe6f1a0623af7a33757e315bd8a76651664c23` (2026-09-12): status/references only; both statements remain `sorry`.
- `gh search` on `google-deepmind/formal-conjectures` for A001818 / `OeisA1818`: PR5568 only (plus unrelated issue 1818 / Serre).
- Epoch `LeanOpenProblems-results`, all three `oeis_1818_conjecture_0` (C1) runs: Anthropic, OpenAI, Google, all `sorryAx`. Google wrote n=1 and n=2 finite expansions then `sorry` for the general statement. Those special-case calculations are not a general proof; n=1 is re-proved here independently. Prefix hits on A181830 are a different sequence.
- AlphaProof Nexus `google-deepmind/alphaproof-nexus-results` `APNOutputs/OEIS` listing (38 files, 2026-09-13): no A001818 / 1818 / A002454 / A356041 file.
- No exact public Lean theorem implying C1 was located in the checked sources. This is bounded absence evidence, not a first-formalization claim.

OEIS editability: not checked in a live editor session; report **unknown**. No OEIS edit attempted.

## Credits

- Mathematics: She, Sun, Xia; Guo, Li, Tao, Wei; Calogero–Perelomov.
- Original Lean statement: The Formal Conjectures Authors.
- New Lean development and write-up: Wentao Li.
- AI assistance: Cursor Grok 4.6 Extra High, 2026-09-13.
- License: Apache 2.0; Copyright 2026 The Formal Conjectures Authors; Copyright 2026 Wentao Li.
