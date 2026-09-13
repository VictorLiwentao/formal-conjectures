#!/usr/bin/env python3
"""Deterministic Fraction search for leftover 10/7 with three odd primes ≥5.

This is evidence, not a Lean proof. Empty output does not resolve A063880.
"""
from fractions import Fraction
import sys

sys.stdout.reconfigure(line_buffering=True)


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0:
            return False
        i += 2
    return True


def next_prime(n: int) -> int:
    p = n + 1
    while not is_prime(p):
        p += 1
    return p


def rho(p: int, a: int) -> Fraction:
    return Fraction(p ** (a + 1) - 1, (p - 1) * (p ** a + 1))


def cap(p: int) -> Fraction:
    return Fraction(p, p - 1)


def last_bound(T: Fraction) -> Fraction:
    if T <= 1:
        return Fraction(0)
    return T / (T - 1)


def max_a(p: int, T: Fraction, amax: int = 30) -> int:
    if rho(p, 2) > T:
        return 1
    a = 2
    while a < amax and rho(p, a + 1) <= T:
        a += 1
    return a


def three_prime_fills(T: Fraction, pmin: int = 5, pmax: int = 200):
    hits = []
    p = pmin if is_prime(pmin) else next_prime(pmin)
    while p <= pmax:
        q0 = next_prime(p)
        r0 = next_prime(q0)
        if cap(p) * cap(q0) * cap(r0) < T:
            print("stop at p", p, "three-cap", cap(p) * cap(q0) * cap(r0))
            break
        a_hi = max_a(p, T)
        for a in range(2, a_hi + 1):
            r1 = rho(p, a)
            if r1 >= T:
                break
            T2 = T / r1
            q = next_prime(p)
            while True:
                r1q = next_prime(q)
                if cap(q) * cap(r1q) < T2 and last_bound(T2) < q:
                    break
                b_hi = max_a(q, T2)
                for b in range(2, b_hi + 1):
                    r2 = rho(q, b)
                    if r2 >= T2:
                        break
                    T3 = T2 / r2
                    lb = last_bound(T3)
                    r = next_prime(q)
                    while r <= int(lb):
                        for c in range(2, 31):
                            r3 = rho(r, c)
                            if r3 == T3:
                                hits.append(((p, a), (q, b), (r, c)))
                            if r3 >= T3:
                                break
                        r = next_prime(r)
                q = next_prime(q)
                if q > 5000:
                    print("INCOMPLETE at q", q, "p", p, "a", a)
                    return hits
        p = next_prime(p)
    return hits


if __name__ == "__main__":
    T = Fraction(10, 7)
    print("T", T)
    print("{7,11,13} cap", cap(7) * cap(11) * cap(13),
          "lt T", cap(7) * cap(11) * cap(13) < T)
    hits = three_prime_fills(T, pmin=5)
    print("omega3 hits pmin=5", hits)
    print("count", len(hits))
