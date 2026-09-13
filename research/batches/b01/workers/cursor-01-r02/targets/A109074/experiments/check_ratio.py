#!/usr/bin/env python3
"""Deterministic checks for the frozen A109074 ratio and valuation prefixes.

These are supporting numerical checks, not a proof.
"""
from math import comb, factorial, gcd


def b_nat(n: int) -> tuple[int, bool]:
    num = 1
    den = 2**n
    for k in range(1, n + 1):
        num *= factorial(6 * k - 2) * factorial(2 * k - 1)
        den *= factorial(4 * k - 1) * factorial(4 * k - 2)
    return num // den, num % den == 0


def frac_reduced(n: int) -> tuple[int, int]:
    if n == 0:
        num, den = 1, 2
    else:
        num = comb(6 * n - 2, 2 * n)
        den = 2 * comb(4 * n - 1, 2 * n)
    g = gcd(num, den)
    return num // g, den // g


def pop(x: int) -> int:
    return bin(x).count("1")


def main() -> None:
    for n in range(0, 12):
        val, exact = b_nat(n)
        assert exact, n
        print("b", n, val)
    for n in range(0, 10):
        fn = frac_reduced(n + 1)
        bn1, _ = b_nat(n + 1)
        bn, _ = b_nat(n)
        g = gcd(bn1, bn)
        ratio = (bn1 // g, bn // g)
        assert fn == ratio, (n, fn, ratio)
        print("ratio", n, fn)
    s = 0
    mn = 0
    for n in range(1, 201):
        s += pop(2 * n - 1) - pop(6 * n - 2)
        mn = min(mn, s)
    print("two_adic_prefix_min_n_le_200", mn)


if __name__ == "__main__":
    main()
