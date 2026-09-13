#!/usr/bin/env python3
"""Classify first injectors of primes q ≡ 2 (mod 3). Experimental only."""

from scan_structure import is_prime, sieve_primes, gcd_from_fac, factor_small
from collections import Counter


def first_k(q: int, mods: list[int], kmax: int) -> tuple[int, int] | None:
    k = min(mods)
    while k <= kmax:
        if k % 6 in mods:
            r = k * q - 2
            if r >= 7 and is_prime(r):
                return k, r
        k += 1
    return None


def c1_and_mceachen(max_n: int) -> None:
    primes = sieve_primes(max_n + 5)
    xfac: Counter[int] = Counter()
    composites = []
    failures = []
    a_vals = {}
    for n in range(1, max_n):
        g = gcd_from_fac(n + 1, xfac, primes)
        an = (n + 1) // g
        a_vals[n] = an
        if an != 1 and not is_prime(an):
            composites.append((n, an))
        inc = 2 + an
        for p, e in factor_small(inc, primes).items():
            xfac[p] += e
    for p in primes:
        if p > max_n:
            break
        if is_prime(p - 2):
            continue
        got = a_vals.get(p - 1)
        if got != p:
            failures.append((p, got))
    print("C1 composite a(n) count", len(composites), "sample", composites[:20])
    print("McEachen failures", failures)


def main() -> None:
    primes = sieve_primes(5000)
    rows = []
    fails5 = []
    fails_all = []
    for q in primes:
        if q < 11 or q % 3 != 2:
            continue
        bound_k = q + 2
        five = 5 * q - 2
        hit5 = five >= 7 and is_prime(five)
        got = first_k(q, [5], bound_k)
        got_all_odd = first_k(q, [1, 3, 5], bound_k)
        # k ≡ 5 (mod 6) only
        got5 = first_k(q, [5], bound_k)
        got35 = first_k(q, [3, 5], bound_k)
        rows.append((q, five, hit5, got5, got35, q * (q + 2) - 1))
        if not hit5:
            fails5.append((q, five, got5, got35))
        if got5 is None:
            fails_all.append(q)
    print("q with 5q-2 composite:", len(fails5), "of", len(rows))
    print("no k≡5 (mod 6) injector in range:", fails_all)
    print("worst k among k≡5 successes:")
    ok = [(q, t[0], t[1], t[1] / q) for q, _, _, t, _, _ in rows if t]
    ok.sort(key=lambda t: t[1], reverse=True)
    for row in ok[:15]:
        print(row)
    print("sample composite 5q-2:")
    for row in fails5[:20]:
        print(row)
    print("--- C1 / McEachen to 30000 ---")
    c1_and_mceachen(40000)


if __name__ == "__main__":
    main()
