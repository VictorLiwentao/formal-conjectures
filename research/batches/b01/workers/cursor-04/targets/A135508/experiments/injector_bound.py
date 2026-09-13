#!/usr/bin/env python3
"""Smallest McEachen injector r ≡ -2 (mod q), r ≡ 2 (mod 3), versus q(q+2)-1.

For primes q ≡ 2 (mod 3), McEachen at p with lpf(p-2)=q is guaranteed if some
such r is ≤ p-3, and the tightest p-3 is q(q+2)-1. Experimental only.
"""

from scan_structure import is_prime, sieve_primes


def first_injector(q: int, limit: int) -> int | None:
    # r = kq - 2, k ≡ 2 (mod 3), k odd, r prime, r ≥ 7
    k = 5  # first odd k ≡ 2 (mod 3) greater than 2
    while True:
        r = k * q - 2
        if r > limit:
            return None
        if r >= 7 and is_prime(r):
            return r
        k += 3  # keeps k ≡ 2 (mod 3); odd+odd=even? 5+3=8 even!
        # k=5,8,11,14,... 8 even gives even r. Skip evens automatically via is_prime
        # Better increment by 6 to keep odd and ≡2 mod 3: 5,11,17,...
        # Wait I did +3 which alternates even/odd. Even k => even r for odd q. Fine to skip.


def first_injector_odd(q: int, limit: int) -> int | None:
    k = 5
    while True:
        r = k * q - 2
        if r > limit:
            return None
        if r >= 7 and is_prime(r):
            return r
        k += 6  # 5,11,17,... all odd and ≡ 2 (mod 3)


def main() -> None:
    primes = sieve_primes(5000)
    fails = []
    rows = []
    for q in primes:
        if q < 11 or q % 3 != 2:
            continue
        bound = q * (q + 2) - 1
        r = first_injector_odd(q, max(bound, 200000))
        ok = r is not None and r <= bound
        rows.append((q, r, bound, ok, None if r is None else r / q))
        if not ok:
            fails.append((q, r, bound))
    print("fails (first r > q(q+2)-1 or missing):", fails[:30], "count", len(fails))
    print("sample:")
    for row in rows[:15]:
        print(row)
    print("largest r/q among successes:")
    okrows = [row for row in rows if row[3]]
    okrows.sort(key=lambda t: t[4] or 0, reverse=True)
    for row in okrows[:10]:
        print(row)


if __name__ == "__main__":
    main()
