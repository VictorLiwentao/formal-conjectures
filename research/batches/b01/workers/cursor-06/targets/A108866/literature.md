# Literature and novelty audit — A108866

Target: `OeisA108866.conjecture` in frozen `FormalConjectures/OEIS/108866.lean`.
SHA-256 of the working and baseline file: `afa95297bd177a882fb72b03f32f1da68ecae58d9126981567562462b73266f8`.
Audit dates: 2026-09-12.

## Exact statement

OEIS A108866 (internal `%C`, Thomas Ordowski, 2020-03-02):

> Conjecture: for n > 3, numerator(-2/n + Sum_{k=1..n} 2^k/k) == 0 (mod n^2) if and only if n is prime.

Lean:

```
theorem conjecture {n : ℕ} (hn : n > 3) :
    (ratExpression n).num ≡ 0 [ZMOD (n^2 : ℤ)] ↔ n.Prime
```

with `ratExpression n = -2/n + ∑_{k=1}^n 2^k/k` for `n > 0`.
`Rat.num` is the reduced numerator, matching OEIS `numerator`.

## Sources checked

### Live OEIS

- https://oeis.org/A108866 and https://oeis.org/A108866/internal
- First fetch of `/internal` succeeded via search cache (2026-09-12). Direct later fetches hit Cloudflare (Ray IDs `a3a29c299f44f268`, `a3a29d216a8ae5e7`).
- `%I A108866 #37 Mar 07 2020 08:54:17`. Last-modified line on the cached internal page: August 13, 2026.
- Related reserved IDs, from OEIS comments and formulas:
  - A332786: `numerator(-1/n + Sum 2^(k-1)/k)`. For odd `n`, OEIS records `a(n) = numerator(-2/n+S(n))/2`. So for odd `n` the A108866 congruence is equivalent to `n^2 | A332786(n)`. Not a new target.
  - A330718: `numerator(Sum (2^k-2)/k)`. Different rational: `T(n) - 2 H_{n-1}`. Same owner reservation; not automatically approved.
- OEIS editability: **unknown**. Public pages required a Cloudflare challenge; no signed-in draft widget was visible. No OEIS edit was attempted.
- b-file: https://oeis.org/A108866/b108866.txt (Harvey P. Dale, n = 0..1000). Head matches Lean tests `a 0..4`.

### DeepMind formal-conjectures

- File introduced in `d7032450` (“Add the first 64 files from AutoOeis”, 2026-08-13).
- GitHub issue/PR search for `108866`, `A108866`, `OeisA108866`: no proof issue or PR.
- Frozen theorem remains `research open` with `sorry`.

### AlphaProof Nexus results

- https://github.com/google-deepmind/alphaproof-nexus-results
- Code search for `108866` in that repo returned no hit on 2026-09-12 (one search 429; directory listing of `APNOutputs/OEIS` had no A108866 name). The repo documents only successful proofs.

### Epoch LeanOpenProblems / results

- Statement copy: `epoch-research/LeanOpenProblems` `apn/data/oeis/Isolated/oeis_a108866_conjecture.lean`.
- Three `$50` runs (`oeis-full-50usd-ant-j0j0g4uzligm1k41`, `...-oai-jajpvieznaevpoyg`, `...-gdm-1s7vwp2si1ap0r6d`) all rejected: `sorryAx`.
- GDM submission (~88 declarations) has useful algebraic scaffolding (`rat_expression_split`, `choose_div_succ`, incomplete `ZMod (p^2)` lemmas) and still `sorry` on the target. Not a solution.

### arXiv / papers

- Komatsu–Sury, arXiv:2309.09491, Proposition 1: for odd prime `p`,
  `(2^{p-1}-1)/p ≡ ∑_{r=1}^{p-1} (-2^{r-1})/r (mod p^2)`.
  Equivalent to `T(p) ≡ 0` in `ℤ_{(p)} / p^2`, i.e. the prime direction of A108866 after `p ∤ T(p).den`.
- Zhi-Hong Sun, J. Number Theory 128 (2008), 280–312: `∑_{k=1}^{p-1} 2^k/k ≡ -2 q_p(2) (mod p^2)` (and a `mod p^3` form). Same prime-direction congruence.
- A. M. Robert, *A Course in p-adic Analysis*, Springer, 2000, p. 278: cited on OEIS A108866; page not independently retrieved here.
- Math.SE 5131013 (2026-03-31): A330718-style `∑ (2^k-2)/k`; accepted answer proves the prime direction via Sun 2008 + Wolstenholme; converse not proved. Claims a computational check to `10^7` for that related sum, not independently rerun here.
- arXiv:2608.11941 (OEIS Open / Epoch language-model paper): no A108866 / A330718 / A332786 in the extracted text.
- MathOverflow searches for this exact numerator-mod-`n^2` iff did not find a thread.

### Prior c5-k4 computation (consulted before any new search)

- https://github.com/Kuberwastaken/c5-k4
- `results/expansion/oeis4_20260826/a108866.md` and `a108866_run1.log` (2026-08-26): exact `Fraction` scan `n = 4..4000`, both directions, plus an lcm-denominator spot check. **No prime fails; no composite passes.**
- Earlier live-search: `n = 4..1200` also clean (`c108866.py`).
- Verdict there: `HOLD_BOUNDED`, not a proof. This worker does not repeat that range as a novelty claim.

## Formalization audit

- Quantifiers: `∀ n > 3`, matching OEIS `n > 3` (not the `n > 4` in some A330718 restatements). `n = 4` is composite and is in scope.
- Reduced numerator: Lean `Rat.num` is reduced; OEIS `numerator` is reduced. Nonvacuity: `n = 4` and `n = 5` exist.
- `ZMOD n^2`: `n > 3` so modulus `≥ 16 > 0`.
- `ratExpression 0 = 0` is unused (`n > 3`).
- Boundary: `n = 4` composite, `T(4) = 61/6`, `16 ∤ 61`. `n = 5`, `T(5) = 50/3`, `25 | 50`.
- No loophole from `n = 0` or empty sums.
- Related A330718 / A332786 are equivalent only after documented rational identities; they stay reserved literature, not extra solve targets.

## Novelty conclusion

No public kernel-checked proof or disproof of the exact frozen iff was found. The prime direction is a published congruence (Sun 2008, Komatsu–Sury 2023). The converse remains open in the checked sources. Failed Epoch runs do not quantify difficulty. This is **not** `prior_solution_found`.
