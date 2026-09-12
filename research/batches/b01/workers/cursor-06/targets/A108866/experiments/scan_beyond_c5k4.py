#!/usr/bin/env python3
"""Targeted checks for A108866 that do not repeat the c5-k4 n=4..4000 scan.

c5-k4 already showed both directions of the reduced-numerator congruence for
every n in 4..4000. This script:

1. Verifies the odd identity T(n) = 2 * sum_{odd r < n} C(n,r)/r.
2. Records 2-adic valuations for even n (structural converse).
3. Records p-adic valuations of T(n) at primes dividing odd composites.
4. Checks Fermat base-2 pseudoprimes and odd composites only for n > 4000.

Unverified relative to Lean: all output here is experimental.
"""
from __future__ import annotations

from fractions import Fraction
from math import comb, gcd
from time import time


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def T(n: int) -> Fraction:
    s = Fraction(0)
    p = 1
    for k in range(1, n + 1):
        p *= 2
        s += Fraction(p, k)
    return s - Fraction(2, n)


def odd_identity_rhs(n: int) -> Fraction:
    return 2 * sum(Fraction(comb(n, r), r) for r in range(1, n, 2))


def v2_int(m: int) -> int:
    if m == 0:
        return 10**9
    m = abs(m)
    v = 0
    while m % 2 == 0:
        m //= 2
        v += 1
    return v


def v2_rat(q: Fraction) -> int:
    if q == 0:
        return 10**9
    return v2_int(q.numerator) - v2_int(q.denominator)


def vp_int(p: int, m: int) -> int:
    if m == 0:
        return 10**9
    m = abs(m)
    v = 0
    while m % p == 0:
        m //= p
        v += 1
    return v


def vp_rat(p: int, q: Fraction) -> int:
    if q == 0:
        return 10**9
    return vp_int(p, q.numerator) - vp_int(p, q.denominator)


def factor_odd(n: int) -> list[tuple[int, int]]:
    fac = []
    m = n
    p = 3
    while p * p <= m:
        e = 0
        while m % p == 0:
            m //= p
            e += 1
        if e:
            fac.append((p, e))
        p += 2
    if m > 1:
        fac.append((m, 1))
    return fac


def holds(n: int) -> bool:
    return T(n).numerator % (n * n) == 0


FERMAT_PSP = [
    341, 561, 645, 1105, 1387, 1729, 1905, 2047, 2465, 2701, 2821, 3277,
    4033, 4369, 4371, 4681, 5461, 6601, 7957, 8321, 8481, 10261, 13741,
    13747, 13981, 14491, 15709, 15841, 16705, 18721, 19951,
]


def main() -> None:
    t0 = time()
    print("=== odd identity T(n) = 2 * sum_{odd r<n} C(n,r)/r for odd n=5..121 ===")
    bad_id = []
    for n in range(5, 122, 2):
        if T(n) != odd_identity_rhs(n):
            bad_id.append(n)
    print(" mismatches:", bad_id if bad_id else "NONE")

    print("=== 2-adic val T(n) for even n=4..80 ===")
    even_bad = []
    for n in range(4, 81, 2):
        q = T(n)
        vt = v2_rat(q)
        vn = v2_int(n)
        ok_num = (q.numerator % (n * n) == 0)
        print(f"  n={n:2d} v2(n)={vn} v2(T)={vt:2d} den_even={q.denominator%2==0} num_even={q.numerator%2==0} holds={ok_num}")
        if ok_num or vt >= 2 * vn:
            even_bad.append(n)
    print(" even n with holds or val too large:", even_bad if even_bad else "NONE")

    print("=== odd composites n=9..199: vp(T) vs 2*vp(n) ===")
    suspicious = []
    for n in range(9, 200, 2):
        if is_prime(n):
            continue
        q = T(n)
        rows = []
        all_ge = True
        for p, e in factor_odd(n):
            v = vp_rat(p, q)
            rows.append((p, e, v, 2 * e))
            if v < 2 * e:
                all_ge = False
        if all_ge or holds(n):
            suspicious.append((n, rows, holds(n)))
        if n in (9, 15, 21, 25, 27, 33, 35, 49, 121, 125, 169):
            print(f"  n={n} holds={holds(n)} vals={rows} num_mod={q.numerator % (n*n)}")
    print(" odd composites with every local val >= 2 e (or holds):", suspicious if suspicious else "NONE")

    print("=== Fermat psp base 2 with n>4000 and n<=19951 ===")
    psp_hits = []
    for n in FERMAT_PSP:
        if n <= 4000:
            continue
        q = T(n)
        h = q.numerator % (n * n) == 0
        print(f"  n={n} prime={is_prime(n)} holds={h} gcd(den,n)={gcd(q.denominator, n)}")
        if h:
            psp_hits.append(n)
    print(" Fermat psp >4000 that hold:", psp_hits if psp_hits else "NONE")

    print("=== odd composites 4001..4500 ===")
    t1 = time()
    hits = []
    scanned = 0
    for n in range(4001, 4501, 2):
        if is_prime(n):
            continue
        scanned += 1
        if holds(n):
            hits.append(n)
            print("  COMPOSITE HOLDS", n)
        if time() - t1 > 90:
            print("  time cap at n", n)
            break
    print(" scanned odd composites:", scanned, "holds:", hits if hits else "NONE")
    print(" elapsed_s", round(time() - t0, 2))


if __name__ == "__main__":
    main()
