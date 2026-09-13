# Proof sketch — `OeisA109074.conjecture`

Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.
Original Lean formalization: The Formal Conjectures Authors.
New Lean proof development and write-up: Wentao Li.
Mathematical credit: Robbins (VSASM product conjecture); Kuperberg, arXiv:math/0008184 (enumeration); Razumov–Stroganov, arXiv:math-ph/0312071 (factorial product).
This is a formalization of known mathematics, not a new enumeration.
AI assistance: Cursor Grok 4.6 Extra High, 2026-09-13.

## Target

```lean
theorem conjecture (n : ℕ) :
    frac (n + 1) = (b (n + 1) : ℚ) / (b n : ℚ)
```

`b` is natural division of

\[
\operatorname{numProd}(n)=\prod_{k=1}^n (6k-2)!\,(2k-1)!,
\qquad
\operatorname{denProd}(n)=2^n\prod_{k=1}^n (4k-1)!\,(4k-2)!.
\]

The Lean proof never replaces `b` by a rational sequence. It proves `denProd n ∣ numProd n` and `0 < b n` first, then applies `Nat.cast_div`.

## Algebra

Binomial identities give, over \(\mathbb{Q}\),

\[
\operatorname{frac}(n+1)=\frac{(6n+4)!\,(2n+1)!}{2\,(4n+3)!\,(4n+2)!}.
\]

This is also the exact rational ratio of successive product terms. After divisibility and positivity, `Nat.cast_div` yields the frozen identity.

## Integrality

`denProd n ∣ numProd n` iff for every prime \(p\),

\[
v_p(\operatorname{numProd} n)\ge v_p(\operatorname{denProd} n).
\]

Legendre’s formula \((p-1)v_p(m!)+s_p(m)=m\) and \((6k-2)+(2k-1)=(4k-1)+(4k-2)\) reduce this to a digit-sum inequality:

\[
\sum_{k=1}^n\bigl(s_p(4k-1)+s_p(4k-2)\bigr)
\ge
\sum_{k=1}^n\bigl(s_p(6k-2)+s_p(2k-1)\bigr)
+(p-1)\cdot\mathbf{1}_{p=2}\cdot n.
\]

### Prime \(p=2\)

Binary identities \(s_2(4k-2)=s_2(2k-1)\) and \(s_2(4k-1)=s_2(2k-1)+1\) reduce the inequality to

\[
\sum_{k=1}^n s_2(2k-1)\ge\sum_{k=1}^n s_2(6k-2).
\]

Simultaneous bounds on the three residue sums of \(s_2\) close by strong induction on even/odd splitting.

### Odd primes

The digit-sum inequality is equivalent to a family of floor inequalities. For each odd modulus \(Q=p^i\),

\[
\sum_{k=1}^n\Bigl(\Bigl\lfloor\frac{4k-1}{Q}\Bigr\rfloor+\Bigl\lfloor\frac{4k-2}{Q}\Bigr\rfloor\Bigr)
\le
\sum_{k=1}^n\Bigl(\Bigl\lfloor\frac{6k-2}{Q}\Bigr\rfloor+\Bigl\lfloor\frac{2k-1}{Q}\Bigr\rfloor\Bigr).
\]

Writing \(r=(2k-1)\bmod Q\), the increment

\[
d(r,Q)=\Bigl\lfloor\frac{3r+1}{Q}\Bigr\rfloor-\Bigl\lfloor\frac{2r+1}{Q}\Bigr\rfloor-\Bigl\lfloor\frac{2r}{Q}\Bigr\rfloor
\]

lies in \(\{-1,0,1\}\). The \(+1\) and \(-1\) residue classes are swapped by \(r\mapsto Q-1-r\), which preserves parity. Prefixes of one period (odd residues, then residue \(0\), then even residues) therefore stay nonnegative. Extending by full periods keeps the count of \(+1\) at least the count of \(-1\).

Termwise \(s_p(2m)+s_p(2m+1)\ge s_p(3m+1)+s_p(m)\) is false. Prefixes are essential.

## Status

`A109074Proof.conjecture` has the exact frozen type. The worker file contains no `sorry`. `#print axioms` reports `propext`, `Classical.choice`, `Quot.sound`. This is a candidate formalization of known mathematics. It is not `independently_verified`.

Failed approaches: termwise integrality of `frac`; per-bit comparison of \(s_2(2k-1)\) vs \(s_2(6k-2)\); crude \(s_2(x+y)\le s_2(x)+s_2(y)\) for the odd \(P/R/U\) step; Kuperberg/PARI products with non-integral intermediate factors.
