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

## Algebra (proved)

Binomial identities give, over \(\mathbb{Q}\),

\[
\operatorname{frac}(n+1)=\frac{(6n+4)!\,(2n+1)!}{2\,(4n+3)!\,(4n+2)!}.
\]

This is also the exact rational ratio of successive product terms. After `denProd n ∣ numProd n` and positivity of `b n`, `Nat.cast_div` yields the frozen identity.

## Integrality

`denProd n ∣ numProd n` iff for every prime \(p\),

\[
v_p(\operatorname{numProd} n)\ge v_p(\operatorname{denProd} n).
\]

Legendre’s formula \( (p-1)v_p(m!)+s_p(m)=m \) and \( (6k-2)+(2k-1)=(4k-1)+(4k-2) \) reduce this to a **digit-sum** inequality:

\[
\sum_{k=1}^n\bigl(s_p(4k-1)+s_p(4k-2)\bigr)
\ge
\sum_{k=1}^n\bigl(s_p(6k-2)+s_p(2k-1)\bigr)
+(p-1)\cdot\mathbf{1}_{p=2}\cdot n.
\]

Per-power floor prefixes can be negative for composite moduli such as \(Q=6\). Prime-power moduli are the relevant case.

### Prime \(p=2\) (proved)

Binary identities \(s_2(4k-2)=s_2(2k-1)\) and \(s_2(4k-1)=s_2(2k-1)+1\) reduce the inequality to

\[
\sum_{k=1}^n s_2(2k-1)\ge\sum_{k=1}^n s_2(6k-2),
\]

equivalently \( C_2(n)\le S_2(n)+n \) where

\[
S_2(n)=\sum_{k<n}s_2(k),\qquad
A_2,B_2,C_2\text{ sum }s_2(3k),\;s_2(3k+1),\;s_2(3k+2).
\]

Binary splitting gives recurrences. The simultaneous bounds

- \(A_2,B_2,C_2\le S_2+n\)
- \(s_2(3n)\le (S_2+n-A_2)+s_2(n)\)
- \(s_2(3n+1)\le (S_2+n-B_2)+s_2(n)+1\)
- \(s_2(3n+2)\le (S_2+n-C_2)+s_2(n)+1\)

close by strong induction on even/odd splitting. The crude estimate \(s_2(3n)\le 2s_2(n)\) is not enough for the odd step; the three popcount comparisons are.

### Odd primes (open in Lean)

Needed: the same digit-sum inequality without the \(2^n\) term. Equivalent floor form: for each \(Q=p^q\),

\[
\Delta_Q(n)=\sum_{k=1}^n d\bigl((2k-1)\bmod Q,Q\bigr)\ge 0,
\]

where \( d(r,Q)=\lfloor(3r+1)/Q\rfloor-\lfloor(2r+1)/Q\rfloor-\lfloor 2r/Q\rfloor\in\{-1,0,1\} \) for \(r<Q\), with

- \(d=1\) iff \(Q\le 3r+1\) and \(2r+1<Q\)
- \(d=-1\) iff \(Q\le 2r\) and \(3r+1<2Q\)

For odd \(Q\), \(r\mapsto Q-1-r\) swaps the \(+1\) and \(-1\) classes and preserves parity. One period of odd residues, then \(0\), then even residues, therefore has equal plus/minus counts and nonnegative prefixes. Composite even moduli such as \(6\) can have negative prefixes; they are not used.

## Status

- `A109074Proof.conjecture` has the exact frozen type, but still depends on the odd-prime digit-sum `sorry`.
- Not a completion. Not `independently_verified`.
- Failed approaches: termwise integrality of `frac`; per-bit comparison of \(s_2(2k-1)\) vs \(s_2(3k+2)\); crude \(s_2(x+y)\le s_2(x)+s_2(y)\) for the odd \(P/R/U\) step; Kuperberg/PARI products with non-integral intermediate factors.
