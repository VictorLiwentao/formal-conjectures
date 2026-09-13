#!/usr/bin/env python3
"""Exact Fraction map of leftover 6/5 ω=2 kernels.

This is evidence for the Lean case split, not a proof of A063880.
Leftover 6/5 is the odd-part equation after v2=3.
"""
from fractions import Fraction

T = Fraction(6, 5)


def rho(p: int, a: int) -> Fraction:
    return Fraction(p ** (a + 1) - 1, (p - 1) * (p ** a + 1))


def cap(p: int) -> Fraction:
    return Fraction(p, p - 1)


def primes_from(start: int, stop: int):
    p = start if start >= 2 else 2
    while p <= stop:
        if all(p % d for d in range(2, int(p ** 0.5) + 1)):
            yield p
        p += 1 if p == 2 else 2 if p > 2 else 1


def rel(prod: Fraction) -> str:
    if prod < T:
        return "under"
    if prod > T:
        return "over"
    return "eq"


def main() -> None:
    print("T = 6/5")
    print("Euler 11/10*13/12", rel(Fraction(11, 10) * Fraction(13, 12)))
    print("rho(125)", rel(rho(5, 3)), float(rho(5, 3)))
    print("7/6*37/36", rel(Fraction(7, 6) * Fraction(37, 36)))
    print()
    print("{5^2, q^2} last square-over / first square-under:")
    last_over = None
    first_under = None
    for q in primes_from(7, 160):
        prod = rho(5, 2) * rho(q, 2)
        if prod > T:
            last_over = q
        elif first_under is None:
            first_under = q
    print(" last over", last_over, "first under", first_under)
    print(" rho(25)*cap(157)", rel(rho(5, 2) * cap(157)))
    print()
    print("{7^a, q^k} selected:")
    for q in [11, 13, 17, 19, 23, 29, 31, 37]:
        print(f" q={q} Euler7*q {rel(Fraction(7, 6) * cap(q))}")
        print(f"  (2,2) {rel(rho(7, 2) * rho(q, 2))}")
        print(f"  (2,3) {rel(rho(7, 2) * rho(q, 3))}")
        print(f"  (3,2) {rel(rho(7, 3) * rho(q, 2))}")
        print(f"  a=2 cap {rel(rho(7, 2) * cap(q))}")
        print(f"  a=3 cap {rel(rho(7, 3) * cap(q))}")


if __name__ == "__main__":
    main()
