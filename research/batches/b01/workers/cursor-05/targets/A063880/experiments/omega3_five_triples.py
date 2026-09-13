#!/usr/bin/env python3
"""Exact Fraction map of leftover 10/7 ω=3 triples that include 5.

This is evidence for the Lean case split, not a proof of A063880.
"""
from fractions import Fraction

T = Fraction(10, 7)


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
    print("T = 10/7")
    print("rho(25)*cap(11)*cap(q) for q>=13 is under leftover:")
    for q in [13, 17, 19, 23, 29]:
        prod = rho(5, 2) * cap(11) * cap(q)
        print(" ", q, rel(prod), float(T - prod))
    print("rho(125)*rho(121)*rho(q^2):")
    for q in [13, 17, 19, 23]:
        prod = rho(5, 3) * rho(11, 2) * rho(q, 2)
        print(" ", q, rel(prod), float(prod - T))
    print("{5^3,7^2,r} squares:")
    for r in primes_from(23, 89):
        prod = rho(5, 3) * rho(7, 2) * rho(r, 2)
        print(" ", r, rel(prod), float(prod - T))
    print("{5^2,7^3,r} squares:")
    for r in primes_from(23, 43):
        prod = rho(5, 2) * rho(7, 3) * rho(r, 2)
        print(" ", r, rel(prod), float(prod - T))
    print("{5^3,7^2,83^k}:")
    for k in range(2, 5):
        prod = rho(5, 3) * rho(7, 2) * rho(83, k)
        print(" ", k, rel(prod), float(prod - T))


if __name__ == "__main__":
    main()
