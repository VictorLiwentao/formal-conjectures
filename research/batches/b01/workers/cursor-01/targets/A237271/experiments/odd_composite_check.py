#!/usr/bin/env python3
"""Deterministic checks of A237271 a(n) on odd composites and Carmichael numbers.

Unverified as a proof. Records finite witnesses only.
"""

from __future__ import annotations

import math
import sys


def sorted_divisors(n: int) -> list[int]:
    if n <= 0:
        return []
    small: list[int] = []
    large: list[int] = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            small.append(i)
            if i * i != n:
                large.append(n // i)
        i += 1
    return small + list(reversed(large))


def a(n: int) -> int:
    divs = sorted_divisors(n)
    count = 0
    for d_k, d_succ in zip(divs, divs[1:]):
        if d_succ % 2 == 1 and d_succ >= 2 * d_k:
            count += 1
    return 1 + count


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


def is_carmichael(n: int) -> bool:
    if n < 2 or is_prime(n):
        return False
    # Korselt: squarefree and p-1 | n-1 for every prime p | n
    m = n
    p = 2
    factors = []
    while p * p <= m:
        if m % p == 0:
            factors.append(p)
            m //= p
            if m % p == 0:
                return False
        p += 1 if p == 2 else 2
    if m > 1:
        factors.append(m)
    if len(factors) < 2:
        return False
    return all((n - 1) % (p - 1) == 0 for p in factors)


def main() -> int:
    odd_comp_fail = []
    for n in range(9, 20000, 2):
        if is_prime(n):
            continue
        val = a(n)
        if val < 3:
            odd_comp_fail.append((n, val))
            break
    carmichael = [n for n in range(1, 30000) if is_carmichael(n)]
    carm_vals = [(n, a(n)) for n in carmichael]
    odd_primes = [(p, a(p)) for p in (3, 5, 7, 11, 13)]
    even_examples = [(n, a(n)) for n in (4, 6, 8, 16, 12)]
    print("odd_composites_lt_20000_min_counterexample", odd_comp_fail)
    print("carmichael_lt_30000_count", len(carmichael))
    print("carmichael_values", carm_vals)
    print("carmichael_min_a", min(v for _, v in carm_vals) if carm_vals else None)
    print("odd_prime_a", odd_primes)
    print("even_examples", even_examples)
    print("a(561)", a(561), "divisors", sorted_divisors(561))
    if odd_comp_fail:
        print("FAIL")
        return 1
    if any(v < 3 for _, v in carm_vals):
        print("FAIL carmichael")
        return 1
    print("PASS finite checks")
    return 0


if __name__ == "__main__":
    sys.exit(main())
