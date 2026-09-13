# Proof plan — A001818-C1

Target: for every `n ≥ 1` and every primitive complex `2n`-th root `ζ`,

```
per M = a n
```

where `M i j = 1` if `i = j`, else `(1 + ζ^(i.val-j.val))/(1 - ζ^(i.val-j.val))`, with **integer** exponent subtraction, `Fin (2n)` indices, and the original `OeisA1818.a`.

Paper Theorem 1.3(ii) even case uses matrix size `N = 2n`. Zero-based Lean indices differ from 1-based paper labels by a simultaneous shift; differences `i-j` are unchanged.

## Informal chain (She–Sun–Xia + Guo–Li–Tao–Wei)

Let `N = 2n` and `x i = ζ^(i.val)`. Then `M` is the transpose of the Cayley kernel `X_{ij} = (x i + x j)/(x i - x j)` (`i ≠ j`), diagonal 1. Permanent is transposition-invariant.

1. **Denominators.** `i ≠ j` implies `N` does not divide `i.val-j.val` as integers with absolute value `< N`, so `ζ^(i-j) ≠ 1`.
2. **Zero-diagonal companion `M - J`.** Off-diagonal `(M-J)_{ij} = 2 ζ^{i-j}/(1-ζ^{i-j})`. Permanent only sums over derangements. Column/row scaling by powers of `ζ` gives
   `per(M-J) = 2^N ∑_{der σ} ∏_i 1/(1-ζ^{σ i - i})`.
3. **Cycle vanishing (Guo Lemma 3.1 / She–Sun–Xia Lemma 5.1).** For length `≥ 3` and distinct `x`-values,
   `∑_{n-cycles τ} ∏ 1/(x_{τ j} - x_j) = 0`.
   Hence in a derangement expansion, any cycle of length `≥ 3` sums to zero. Remaining terms are fixed-point-free involutions when relating `per(X-J)` to perfect matchings.
4. **Sign cancellation (Guo Thm 3.2, even size).** One sign class of the zero-diagonal circulant vanishes, so the unsigned derangement sum equals `±` the signed sum (the determinant).
5. **Calogero–Perelomov / Fourier.** The circulant `A_{ij} = 0` on the diagonal and `2/(1-ζ^{i-j})` off it has eigenvalues `{N-1, N-3, …, 1-N}`. Product is `(-1)^n ((2n-1)!!)^2`. Then `A = 2B` with `B_{ij} = (1-δ)/(1-ζ^{i-j})`, so
   `∑_{der} sign(σ) ∏ 1/(1-ζ^{σ i - i}) = (-1)^n (a n) / 2^N`.
   Combined with (4) this is Guo–Li–Tao–Wei (1.1) / Lemma 5.2(i):
   `∑_{der} ∏ 1/(1-ζ^{σ i - i}) = (a n) / 2^N`.
   Hence `per(M-J) = a n`.
6. **`per M = per(M-J)`.** She–Sun–Xia Theorem 1.3(i): for the even-order Cayley kernel, `per X = per(X-J) = S(x)`. Proof uses:
   - odd-cycle cancellation via `f(τ^{-1}) = (-1)^{#D(τ)} f(τ)` (Lemma 2.2);
   - even full-cycle sums constant (Lemma 2.3);
   - vanishing of `S` if some `x_i = 0` (sign-matrix permanent zero, Lemma 3.1), giving the binomial identity for those constants;
   - recurrence `S(x_1,…,x_{2n}) = ∑_{i≠1} (1+f((1 i))) S(omit 1 and i)`;
   - induction to the matching formula Theorem 1.1, which equals both `per X` and `per(X-J)`.
   Tangent-number generating functions (Theorem 1.2) are **not** required for C1; only the binomial identity (3.8)/(3.9) from vanishing is used.
7. Therefore `per M = a n`.

A circulant permanent is not a product of eigenvalues. Eigenvalues are used only for the **determinant** of the zero-diagonal companion, plus a proved sign-cancellation identity.

## Edge cases

- `n = 1`: `ζ = -1`, `M = I_2`, `per = 1 = a 1`. Proved directly.
- Empty product in `a 0` is unused (`hn : 1 ≤ n`).
- Division by zero is excluded by (1).
- Primitive roots other than `e^{2π i / N}`: all arguments are Galois/algebraic in `ζ` (`ζ^N = 1` and `ζ^k = 1 ↔ N ∣ k`), so every primitive root is covered.

## Lean route

Do not import or use `OeisA1818.conjecture1` (`sorry`). Use original `a`. Prove a wrapper whose type is definitionally the frozen statement. Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Formalized so far

- Denominators and `n=1`.
- Calogero kernel sums via the finite geometric identity `1/(1-ζ^k) = -N⁻¹ ∑_{j=1}^{N-1} j (ζ^k)^j`.
- Fourier Vandermonde diagonalization: `calogero * F = F * diag(N-1-2r)`.
- `det calogero = (-1)^n a n`.
- Signed derangement sum of `(1-ζ^{σi-i})⁻¹` equals that determinant over `2^{2n}`.
- `per(M-J) = 2^{2n}` times the corresponding unsigned derangement sum, using `∏ ζ^{σi-i}=1`.
- Guo Lemma 3.1 class sum: inserting a point on one edge of a remaining cycle multiplies by a telescoping kernel; rotating the tail after a fixed point sums to zero (`sum_cycleEdgeWeight_cons_rotate`). The paper's displayed `λ_i/λ_1` product is not used; the kernel is `(z_{k+1}-z_k)/((w-z_k)(z_{k+1}-w))`.
- Guo Lemma 3.1 global form: the sum of those insertion weights over all listings of the remaining points is zero (`sum_cycleEdgeWeight_ncycles`).
- Transfer identity: on the support of `σ`, `(ζ^{σ i} - ζ^i)⁻¹ = (-ζ^i)⁻¹ (1 - ζ^{σ i - i})⁻¹` (`cycleEdgeWeight_zeta`). Listings through a fixed point are N-cycles with full support.
- Bijection `listingEquiv`: listings of the remaining points after a fixed `p` correspond to `{σ | σ.IsCycle ∧ σ.support = univ}`. Inverse sends `σ` to the listing `(σ p, σ² p, …)`. The `(1-ζ)^{-1}` weights of all N-cycles therefore sum to 0 (`ncycle_inv_one_sub_sum`).
- Mixed long cycles: `ofSubtype` lifts a cycle on a subset; holding the complementary permutation fixed, the sum over listings of that subset vanishes (`sum_cycleEdgeWeight_replace_cycle`). The same vanishing transfers to `(1-ζ)^{-1}` weights (`inv_one_sub_replace_cycle`). A full-support permutation either has a cycle of length at least 3 or is a product of `n` transpositions, and the latter have sign `(-1)^n`. Remainder support after removing a cycle factor is the complement. Permutations split by the distinguished long-cycle key `longKey`.
