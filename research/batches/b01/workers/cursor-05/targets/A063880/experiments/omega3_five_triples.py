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
    print("{5,13,19} mixed remaining a>=4, b>=3:")
    for a, b, c in [(4, 3, 2), (5, 4, 3), (6, 3, 4), (5, 3, 4)]:
        prod = rho(5, a) * rho(13, b) * rho(19, c)
        print(" ", (a, b, c), rel(prod), float(prod - T))
    print("{5^4,7^2,p^2} last over / first under:")
    last_over = None
    first_under = None
    for p in primes_from(23, 250):
        prod = rho(5, 4) * rho(7, 2) * rho(p, 2)
        if prod > T:
            last_over = p
        elif first_under is None:
            first_under = p
            break
    print(" last_over", last_over, "first_under", first_under)
    print("{5^2,7^4,p} squares/cap at 31,37,41:")
    for p in [23, 29, 31, 37, 41]:
        print(" ", p, "sq", rel(rho(5, 2) * rho(7, 4) * rho(p, 2)),
              "cap", rel(rho(5, 2) * rho(7, 4) * cap(p)))


if __name__ == "__main__":
    main()
