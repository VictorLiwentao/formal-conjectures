#!/usr/bin/env python3
"""First-order Bonferroni/Mertens count for leftover square-window injectors.

Experimental only; not a Lean proof. For q ≡ 2 (mod 3) the square-window
candidates are k ≡ 5 (mod 6), k ≤ q+2, equivalently n = kq-2 ≤ q(q+2)-1.
A is that set of n. A_p is those n divisible by a prime p < q.

If |A| > ∑_p |A_p| then A is nonempty after a first-order union bound.
The harmonic sum ∑_{p<q} 1/p → ∞, so this test is not a ∀q proof.
"""

from __future__ import annotations

import sys
from math import isqrt


def sieve(n: int) -> bytearray:
    s = bytearray(b"\x01") * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, isqrt(n) + 1):
        if s[i]:
            start = i * i
            s[start : n + 1 : i] = b"\x00" * ((n - start) // i + 1)
    return s


def candidates(q: int) -> list[int]:
    out = []
    if q % 3 == 2:
        k = 5
    elif q % 3 == 1:
        k = 7
    else:
        return out
    while k <= q + 2:
        n = k * q - 2
        if n % 3 == 2:
            out.append(n)
        k += 6
    return out


def main() -> None:
    qs = [int(x) for x in sys.argv[1:]] or [
        113,
        131,
        149,
        157,
        173,
        191,
        197,
        227,
        251,
        389,
        1009,
        5003,
    ]
    sp = sieve(max(qs) + 10)
    primes = [i for i in range(2, max(qs) + 10) if sp[i]]
    print("q |A| sum|A_p| |U| unsifted bound_ok")
    for q in qs:
        A = candidates(q)
        a = set(A)
        hit = 0
        marked = set()
        for p in primes:
            if p >= q:
                break
            ap = [n for n in A if n % p == 0]
            hit += len(ap)
            marked.update(ap)
        unsifted = [n for n in A if n not in marked]
        u = len(A) - len(marked)
        print(q, len(A), hit, u, len(unsifted), int(hit < len(A)))


if __name__ == "__main__":
    main()
