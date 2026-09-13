#!/usr/bin/env python3
"""Leading-term p-adic data for T(p^e) via the odd binomial sum.

Experimental only. Unverified relative to Lean.

For odd n, T(n) = 2 n * S, S = sum_{odd r < n} C(n-1, r-1) / r^2.
For n = p^e the unique-min valuation among odd r is e-1, achieved at
r = a p^{e-1} for odd a in 1..p-1. For p=3 that a is unique (a=1).
For p>=5 the leading units are
U = sum_{a odd, 1<=a<p} C(p^e-1, a p^{e-1}-1) / a^2.
If v_p(U)=0 then v_p(T)=2-e; if v_p(U)=1 then v_p(T)=3-e (next layer is +2).
"""
from __future__ import annotations

from math import comb, gcd


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


def U_num_den(p: int, e: int) -> tuple[int, int]:
    """Return (A, B) with U = A/B in lowest terms, B coprime to p."""
    pe1 = p ** (e - 1)
    num = 0
    den = 1
    for a in range(1, p, 2):
        C = comb(p**e - 1, a * pe1 - 1)
        # U += C / a^2
        num = num * (a * a) + C * den
        den *= a * a
        g = gcd(num, den)
        num //= g
        den //= g
    return num, den


def main() -> None:
    print("=== p=3 unique odd multiple of 3^{e-1} below 3^e ===")
    for e in range(2, 8):
        n = 3**e
        r0 = 3 ** (e - 1)
        odds = [r for r in range(1, n, 2) if r % (3 ** (e - 1)) == 0]
        print(f"  e={e} n={n} unique={odds == [r0]} odds={odds}")

    print("=== v_p(U) for odd primes p<=23, e=2,3,4 ===")
    for p in range(3, 24, 2):
        if not is_prime(p):
            continue
        for e in (2, 3, 4):
            if p == 3 and e >= 2:
                # unique min; U is a single p-unit
                a = 1
                C = comb(p**e - 1, p ** (e - 1) - 1)
                print(f"  p={p} e={e} single C v={vp(p, C)} C%p={C % p}")
                continue
            A, B = U_num_den(p, e)
            v = vp(p, A) - vp(p, B)
            print(f"  p={p} e={e} v_p(U)={v}  B_vp={vp(p, B)}  A%p={A % p if v == 0 else 'p|A'}")

    print("=== predicted v_p(T(p^e)) vs 2e for p<=19, e=2,3 ===")
    # v(T) = e + v(S), v(S) = -2(e-1) + v(U) if v(U) < 2
    for p in range(3, 20, 2):
        if not is_prime(p):
            continue
        for e in (2, 3):
            if p == 3:
                vU = 0
            else:
                A, B = U_num_den(p, e)
                vU = vp(p, A) - vp(p, B)
            pred = (2 - e) + vU  # if vU < 2
            print(f"  p={p} e={e} vU={vU} pred_vT={pred} 2e={2*e} ok={pred < 2*e}")


if __name__ == "__main__":
    main()
