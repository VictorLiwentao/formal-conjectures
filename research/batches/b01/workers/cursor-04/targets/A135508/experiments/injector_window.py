#!/usr/bin/env python3
"""Search for a square-window injector failure or McEachen counterexample.

Experimental only; not a Lean proof. Tracks factorizations of x(n), not x(n).
"""

from __future__ import annotations

import math
from collections import Counter

from scan_structure import factor_small, gcd_from_fac, is_prime, sieve_primes


def first_injector_k(q: int, kmax: int) -> tuple[int, int] | None:
    k = 5
    while k <= kmax:
        r = k * q - 2
        if r >= 7 and is_prime(r):
            return k, r
        k += 6
    return None


def v3(n: int) -> int:
    e = 0
    while n % 3 == 0:
        n //= 3
        e += 1
    return e


def main() -> None:
    primes = sieve_primes(30000)
    window_fails = []
    worst = []
    for q in primes:
        if q < 11 or q % 3 != 2:
            continue
        bound_k = q + 2
        got = first_injector_k(q, bound_k)
        if got is None:
            window_fails.append(q)
            continue
        k, r = got
        worst.append((k, q, r, r / q))
    worst.sort(reverse=True)
    print("window failures k>q+2 for q<=30000 q=2 (mod 3):", window_fails)
    print("worst k:", worst[:12])

    max_n = 80000
    primes_n = sieve_primes(max_n + 5)
    xfac: Counter[int] = Counter()
    composites = []
    three_div = []
    v3_fail = []
    failures = []
    a_vals = {}
    first_entry: dict[int, int] = {}
    for n in range(1, max_n):
        g = gcd_from_fac(n + 1, xfac, primes_n)
        an = (n + 1) // g
        a_vals[n] = an
        if n >= 3 and an % 3 == 0:
            three_div.append((n, an))
        vx = xfac.get(3, 0)
        if v3(n + 1) > vx:
            v3_fail.append((n, v3(n + 1), vx, an))
        if an != 1 and not is_prime(an):
            composites.append((n, an))
        inc = 2 + an
        for p, e in factor_small(inc, primes_n).items():
            if p not in first_entry:
                first_entry[p] = n + 1
            xfac[p] += e
    for p in primes_n:
        if p > max_n:
            break
        if is_prime(p - 2):
            continue
        got = a_vals.get(p - 1)
        if got != p:
            failures.append((p, got))
    print("McEachen failures to", max_n, failures)
    print("C1 composite a(n) count", len(composites), "sample", composites[:15])
    print("3 | a(n) for n>=3 count", len(three_div), "sample", three_div[:10])
    print("v3(n+1)>v3(x n) count", len(v3_fail), "sample", v3_fail[:10])
    leftover = []
    for p in primes_n:
        if p > max_n or p < 7 or p % 3 != 1 or is_prime(p - 2):
            continue
        q = min(factor_small(p - 2, primes_n))
        if q <= 101:
            continue
        if is_prime(q - 2) and q >= 13:
            continue
        n0 = first_entry.get(q)
        leftover.append((p, q, n0, p - 3, n0 is not None and n0 <= p - 3))
    miss = [row for row in leftover if not row[4]]
    print("remaining-class leftover with lpf>101 not twin", len(leftover), "missed entry", miss[:20])


if __name__ == "__main__":
    main()
