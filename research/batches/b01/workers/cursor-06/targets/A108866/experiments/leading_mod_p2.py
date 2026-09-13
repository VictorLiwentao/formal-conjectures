#!/usr/bin/env python3
"""Experimental: C(p^e-1, a p^{e-1}-1) vs C(p-1, a-1) mod p^2,
and the odd sums sigma = sum 1/a^2, tau = sum H_{a-1}/a^2.

Unverified relative to Lean.
"""
from __future__ import annotations

from math import comb, gcd
from fractions import Fraction


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def vp(p: int, m: int) -> int:
    if m == 0:
        return 10**9
    m = abs(m)
    v = 0
    while m % p == 0:
        m //= p
        v += 1
    return v


def vp_frac(p: int, q: Fraction) -> int:
    return vp(p, q.numerator) - vp(p, q.denominator)


def H(n: int) -> Fraction:
    return sum((Fraction(1, k) for k in range(1, n + 1)), Fraction(0))


def main() -> None:
    print("=== C(p^e-1, a p^{e-1}-1) - C(p-1, a-1)  valuation ===")
    for p in range(5, 20, 2):
        if not is_prime(p):
            continue
        for e in (2, 3):
            diffs = []
            for a in range(1, p, 2):
                C = comb(p**e - 1, a * p ** (e - 1) - 1)
                C0 = comb(p - 1, a - 1)
                diffs.append(vp(p, C - C0))
            print(f"  p={p} e={e} min_v(C-C0)={min(diffs)} vals={diffs}")

    print("=== v_p(sigma), v_p(tau), v_p(sigma - p tau) for odd a < p ===")
    for p in range(5, 40, 2):
        if not is_prime(p):
            continue
        sigma = sum((Fraction(1, a * a) for a in range(1, p, 2)), Fraction(0))
        tau = sum((H(a - 1) / (a * a) for a in range(1, p, 2)), Fraction(0))
        combo = sigma - p * tau
        print(
            f"  p={p} v(sigma)={vp_frac(p, sigma)} v(tau)={vp_frac(p, tau)} "
            f"v(sigma-p tau)={vp_frac(p, combo)}"
        )


if __name__ == "__main__":
    main()
