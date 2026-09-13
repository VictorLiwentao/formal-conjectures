#!/usr/bin/env python3
"""Type B leftover remaining primes: every prime factor of p-2 is ≡ 2 (mod 3).

Experimental only; not a Lean proof. Cube lemma: such n satisfies n ≥ lpf(n)^3.
The example p = 113^3 + 2 is Type B, but 113 now has a proved k=5 injector.
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
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 2000000
    sp = sieve(n + 10)
    fb_lim = max(isqrt(n) + 20, 2000)
    spf = sieve(fb_lim)
    primes = [i for i in range(2, fb_lim + 1) if spf[i]]
    type_b = []
    leftover = 0
    for p in range(7, n):
        if not sp[p] or p % 3 != 1:
            continue
        m = p - 2
        if m < len(sp) and sp[m]:
            continue
        if miller_rabin(m):
            continue
        q = min_fac(m, primes)
        if miller_rabin(q - 2):
            continue
        if q < 113:
            continue
        leftover += 1
        facs = factors(m, primes)
        if facs and all(r % 3 == 2 for r in facs):
            type_b.append((p, q, facs, m >= q * q * q))

    print(f"leftover remaining p < {n}, lpf>=113 not twin: {leftover}")
    print(f"Type B among them: {len(type_b)}")
    if type_b:
        print("first Type B:", type_b[:15])
        print("all cube bounds hold:", all(t[-1] for t in type_b))
        print("Type B minFacs:", sorted({t[1] for t in type_b}))


if __name__ == "__main__":
    main()
