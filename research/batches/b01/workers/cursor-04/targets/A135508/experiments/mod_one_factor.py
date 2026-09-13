#!/usr/bin/env python3
"""Leftover complementary factors ≡ 1 (mod 3) and the k=7 injector.

Experimental only; not a Lean proof.

An odd composite n ≡ 2 (mod 3) with n < lpf(n)^3 cannot be a product of
only primes ≡ 2 (mod 3): that would need at least three such factors.
Remaining leftover p-2 with lpf ≡ 2 (mod 3) and p-2 < q^3 therefore has
a prime factor r ≡ 1 (mod 3). The k=7 injector 7r-2 always fits in the
McEachen window for remaining p once 5 does not divide p-2.
"""

from __future__ import annotations

import sys
from math import isqrt


def miller_rabin(n: int) -> bool:
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0:
        return False
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 23):
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def sieve(n: int) -> bytearray:
    s = bytearray(b"\x01") * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, isqrt(n) + 1):
        if s[i]:
            start = i * i
            s[start : n + 1 : i] = b"\x00" * ((n - start) // i + 1)
    return s


def min_fac(n: int, primes: list[int]) -> int:
    for p in primes:
        if p * p > n:
            return n
        if n % p == 0:
            return p
    return n


def factors(n: int, primes: list[int]) -> list[int]:
    out = []
    m = n
    for p in primes:
        if p * p > m:
            break
        if m % p == 0:
            out.append(p)
            while m % p == 0:
                m //= p
    if m > 1:
        out.append(m)
    return out


def main() -> None:
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 400000
    sp = sieve(n + 10)
    primes = [i for i in range(2, n + 10) if sp[i]]
    leftover = []
    type_b = []
    cube_fail = []
    seven_hit = 0
    seven_miss = []
    for p in range(7, n):
        if not sp[p] or p % 3 != 1:
            continue
        m = p - 2
        if sp[m]:
            continue
        q = min_fac(m, primes)
        if miller_rabin(q - 2):
            continue
        if q < 113:
            continue
        facs = factors(m, primes)
        mod1 = [r for r in facs if r % 3 == 1]
        mod2 = [r for r in facs if r % 3 == 2]
        leftover.append((p, q, m // q, facs, mod1, mod2))
        if not mod1:
            type_b.append((p, q, facs))
        if q % 3 == 2 and m < q * q * q and not mod1:
            cube_fail.append((p, q, facs))
        if mod1 and any(miller_rabin(7 * r - 2) for r in mod1):
            seven_hit += 1
        elif mod1:
            seven_miss.append((p, q, mod1))

    print(f"leftover remaining p < {n}: {len(leftover)}")
    print(f"with a factor ≡ 1 (mod 3): {len(leftover) - len(type_b)}")
    print(f"Type B, all factors ≡ 2 (mod 3): {len(type_b)}")
    if type_b:
        print("first Type B:", type_b[:10])
    print(f"cube-lemma failures (should be 0): {len(cube_fail)}")
    if cube_fail:
        print("first cube failures:", cube_fail[:10])
    print(f"some ≡1 factor has prime 7r-2: {seven_hit} / {len(leftover)}")
    print(f"missed by every 7r-2 of ≡1 factors: {len(seven_miss)}")
    if seven_miss:
        print("first 7r-2 misses:", seven_miss[:15])

    q113 = 113
    print(f"113^3 = {q113 ** 3}; Type B requires p-2 >= q^3 for leftover q")


if __name__ == "__main__":
    main()
