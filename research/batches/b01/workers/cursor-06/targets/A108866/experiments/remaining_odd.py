#!/usr/bin/env python3
"""Odd composites that the kernel L-criterion and m<q test do not cover.

Experimental only. Does not repeat the c5-k4 n=4..4000 hold/fail scan.
Unverified relative to Lean.

A number n is marked covered if some odd prime p dividing n satisfies
either:
  - m = n/p is not divisible by p, p <= m, and L(m / p^e) != 0 in F_p
    where e = floor(log_p m);
  - or m < p and p does not divide T(m).num.

Prime powers fail the first test because p divides m. Products such as
13*79 fail both: L(6)=0 in F_13 and 79 divides T(13).num.
"""
from __future__ import annotations

from fractions import Fraction
from functools import lru_cache


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


@lru_cache(None)
def T(n: int) -> Fraction:
    return -Fraction(2, n) + sum(Fraction(1 << k, k) for k in range(1, n + 1))


def L(r: int, p: int) -> int:
    s = 0
    for j in range(1, r + 1):
        s = (s + pow(2, j, p) * pow(j, -1, p)) % p
    return s


def factor_odd(n: int) -> list[tuple[int, int]]:
    fac = []
    x = n
    p = 3
    while p * p <= x:
        e = 0
        while x % p == 0:
            x //= p
            e += 1
        if e:
            fac.append((p, e))
        p += 2
    if x > 1:
        fac.append((x, 1))
    return fac


def covered(n: int) -> tuple[bool, object]:
    fac = factor_odd(n)
    for p, _e in fac:
        m = n // p
        if m % p == 0:
            continue
        if m < p:
            if T(m).numerator % p != 0:
                return True, f"m={m}<{p} and p not div T(m).num"
            continue
        ee = 0
        pp = 1
        while pp * p <= m:
            pp *= p
            ee += 1
        r = m // pp
        if L(r, p) != 0:
            return True, f"L({r}) ne 0 at p={p} e={ee}"
    return False, fac


def main() -> None:
    remain = []
    for n in range(5, 2001, 2):
        if is_prime(n):
            continue
        ok, why = covered(n)
        if not ok:
            remain.append((n, why))
    print("remaining odd composites n<=2000:", len(remain))
    for n, w in remain:
        print(n, w)


if __name__ == "__main__":
    main()
