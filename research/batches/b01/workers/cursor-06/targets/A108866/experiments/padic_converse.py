#!/usr/bin/env python3
"""p-adic valuations of T(n) for the A108866 odd-composite converse.

Does not repeat the c5-k4 n=4..4000 hold/fail scan as a novelty claim.
Computes v_p(T(n)) by summing 2^k/k in Z/p^M after clearing p-powers.

Unverified relative to Lean.
"""
from __future__ import annotations

from math import gcd


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


def vp(p: int, m: int) -> int:
    if m == 0:
        return 10**9
    m = abs(m)
    v = 0
    while m % p == 0:
        m //= p
        v += 1
    return v


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


def padic_val_T(n: int, p: int, prec: int = 12) -> int:
    """Return v_p(T(n)) with T = sum_{k=1}^n 2^k/k - 2/n.

    Stores p^offset * T as an integer modulo p^M, then reads off the valuation.
    offset is large enough that every term p^offset * 2^k/k is a p-integer.
    """
    assert p % 2 == 1 and is_prime(p)
    max_vk = 0
    k = p
    while k <= n:
        max_vk += 1
        k *= p
    offset = max_vk + 2
    M = offset + prec + 4
    mod = p**M
    acc = 0
    for k in range(1, n):
        v = vp(p, k)
        a = k // p**v
        e = offset - v
        term = pow(2, k, mod) * pow(a, -1, mod) % mod
        term = term * pow(p, e, mod) % mod
        acc = (acc + term) % mod
    # Fermat term (2^n - 2)/n
    vn = vp(p, n)
    an = n // p**vn
    num = (pow(2, n, p ** (M + vn + 2)) - 2)
    # exact 2^n-2 in Z, reduce after removing p-powers from the numerator
    two_n = pow(2, n)
    num_exact = two_n - 2
    vnum = vp(p, num_exact)
    unit_num = (num_exact // p**vnum) % mod
    eF = offset + vnum - vn
    termF = unit_num * pow(an, -1, mod) % mod
    if eF >= 0:
        termF = termF * pow(p, eF, mod) % mod
    else:
        raise RuntimeError("fermat term below offset", n, p, eF)
    acc = (acc + termF) % mod
    if acc == 0:
        return prec  # lower bound only; treat as "too large"
    v_acc = 0
    tmp = acc
    while tmp % p == 0:
        tmp //= p
        v_acc += 1
    return v_acc - offset


def primes_upto(limit: int) -> list[int]:
    out = []
    for p in range(3, limit + 1, 2):
        if is_prime(p):
            out.append(p)
    return out


def main() -> None:
    print("=== v_p(T(p^2)) for odd primes p with p^2 <= 3721 ===")
    rows = []
    for p in primes_upto(61):
        n = p * p
        v = padic_val_T(n, p, prec=8)
        rows.append((p, n, v, 4, v < 4))
        print(f"  p={p:3d} n={n:5d} v_p(T)={v:3d} 2e=4  converse_at_p={v < 4}")
    print(" any p^2 with v>=4:", [r for r in rows if not r[4]] or "NONE")

    print("=== v_p(T(p^3)) for p^3 <= 2197 (13^3) ===")
    for p in [3, 5, 7, 11, 13]:
        n = p**3
        v = padic_val_T(n, p, prec=10)
        print(f"  p={p} n={n} e=3 2e=6 v={v} converse={v < 6}")

    print("=== odd composites n=9..199: min_p (2e - v_p(T)) ===")
    tight = []
    for n in range(9, 200, 2):
        if is_prime(n):
            continue
        gaps = []
        for p, e in factor_odd(n):
            v = padic_val_T(n, p, prec=8)
            gaps.append((p, e, v, 2 * e - v))
        best = min(g[3] for g in gaps)
        if best <= 1:
            tight.append((n, gaps))
            print(f"  tight n={n} gaps={gaps}")
    print(" composites with some local gap <=1:", tight if tight else "NONE")
    print(" (gap = 2e - v_p(T); converse holds iff some gap > 0)")

    print("=== square-free n=pq, p<q, n<=399: v at p and q ===")
    small_p = primes_upto(40)
    for i, p in enumerate(small_p):
        for q in small_p[i + 1 :]:
            n = p * q
            if n > 399:
                continue
            vp_ = padic_val_T(n, p, prec=6)
            vq_ = padic_val_T(n, q, prec=6)
            ok = vp_ < 2 or vq_ < 2
            if not ok or min(vp_, vq_) >= 1:
                print(f"  n={n}={p}*{q} v_p={vp_} v_q={vq_} ok={ok}")


if __name__ == "__main__":
    main()
