#!/usr/bin/env python3
"""Exact Fraction map of leftover 6/5 ω=3 kernels.

This is evidence for the Lean case split, not a proof of A063880.
"""
from fractions import Fraction
from itertools import combinations

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
    print("{5^2,7^2}", rel(rho(5, 2) * rho(7, 2)))
    print("{11^2,13^2,17^2}", rel(rho(11, 2) * rho(13, 2) * rho(17, 2)))
    print()
    print("{11^2,13^2,p^2} last over / first under:")
    last_over = None
    first_under = None
    for p in primes_from(17, 80):
        prod = rho(11, 2) * rho(13, 2) * rho(p, 2)
        cprod = rho(11, 2) * rho(13, 2) * cap(p)
        if prod > T:
            last_over = p
        elif first_under is None:
            first_under = p
        if p in (17, 43, 47) or rel(prod) != rel(cprod):
            print(" ", p, "sq", rel(prod), "cap", rel(cprod))
    print(" last over", last_over, "first under", first_under)
    print()
    print("omega=3 primes >=11, p<q<r<=47 square-over count:")
    n_over = n_under = 0
    for p, q, r in combinations(list(primes_from(11, 47)), 3):
        prod = rho(p, 2) * rho(q, 2) * rho(r, 2)
        if prod > T:
            n_over += 1
        else:
            n_under += 1
    print(" over", n_over, "under", n_under)


if __name__ == "__main__":
    main()
