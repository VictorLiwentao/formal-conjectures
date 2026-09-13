#!/usr/bin/env python3
"""Miller–Rabin search for a square-window injector failure.

Experimental only; not a Lean proof. For primes q ≡ 2 (mod 3), look for the
least k ≡ 5 (mod 6) with kq-2 prime. A window failure is k > q+2.

A McEachen counterexample would additionally need a prime p with lpf(p-2)=q
and p-3 below the first injector (tightest: p = q(q+2)+2 prime, q+2 composite,
and no coprime composite injector). This script only flags window failures.
"""

from __future__ import annotations

import sys


def miller_rabin(n: int) -> bool:
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 23, 29, 31)
    for p in small:
        if n == p:
            return True
        if n % p == 0:
            return False
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    # Deterministic for n < 2^64.
    for a in (2, 3, 5, 7, 11, 13, 23):
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def sieve_primes(limit: int) -> list[int]:
    mark = bytearray(b"\x01") * (limit + 1)
    mark[0:2] = b"\x00\x00"
    for i in range(2, int(limit**0.5) + 1):
        if mark[i]:
            mark[i * i : limit + 1 : i] = b"\x00" * len(range(i * i, limit + 1, i))
    return [i for i, v in enumerate(mark) if v]


def first_injector_k(q: int, kmax: int) -> tuple[int, int] | None:
    k = 5
    while k <= kmax:
        r = k * q - 2
        if r >= 7 and miller_rabin(r):
            return k, r
        k += 6
    return None


def main() -> None:
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
    primes = sieve_primes(limit)
    fails = []
    fails8 = []
    worst: list[tuple[int, int, int]] = []
    tight_candidates = []
    for q in primes:
        if q < 11 or q % 3 != 2:
            continue
        got = first_injector_k(q, q + 2)
        if got is None:
            fails.append(q)
            if first_injector_k(q, q + 8) is None:
                fails8.append(q)
            r_next = first_injector_k(q, 50 * q)
            tight = q * (q + 2) + 2
            tight_candidates.append(
                (q, r_next, tight, miller_rabin(tight), miller_rabin(q + 2))
            )
            continue
        k, r = got
        worst.append((k, q, r))
    worst.sort(reverse=True)
    print(f"limit={limit}")
    print("window failures k>q+2:", fails)
    print("window failures k>q+8:", fails8)
    print("worst k:", worst[:15])
    if tight_candidates:
        print("tight p=q(q+2)+2 for failures:", tight_candidates[:20])


if __name__ == "__main__":
    main()
