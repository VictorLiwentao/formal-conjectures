#!/usr/bin/env python3
"""McEachen-window injectors for leftover remaining primes.

Experimental only; not a Lean proof. Remaining leftover means p ≡ 1 (mod 3),
p-2 composite, lpf(p-2) ≥ 107, and that least factor is not a larger twin.

For each prime factor r of p-2, an admissible k with k*r-2 prime and
k ≤ (p-2)/r injects r by index k*r-2 ≤ p-3. A McEachen counterexample
candidate would need no such k for any prime factor of p-2.
"""

from __future__ import annotations

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


def first_injector(r: int, kmax: int) -> tuple[int, int] | None:
    if r % 3 == 2:
        k, step = 5, 6
    elif r % 3 == 1:
        k, step = 7, 6
    else:
        return None
    while k <= kmax:
        rinj = k * r - 2
        if rinj > 3 and rinj % 3 == 2 and miller_rabin(rinj):
            return k, rinj
        k += step
    return None


def covered_by_k(p: int, facs: list[int], k_mod2: list[int], k_mod1: list[int]) -> bool:
    for r in facs:
        kmax = (p - 2) // r
        ks = k_mod2 if r % 3 == 2 else k_mod1
        for k in ks:
            if k <= kmax:
                rinj = k * r - 2
                if rinj > 3 and rinj % 3 == 2 and miller_rabin(rinj):
                    return True
    return False


def main() -> None:
    n = 200000
    sp = sieve(n + 10)
    primes = [i for i in range(2, n + 10) if sp[i]]
    leftover: list[tuple[int, int, int, list[int]]] = []
    for p in range(7, n):
        if not sp[p] or p % 3 != 1:
            continue
        m = p - 2
        if sp[m]:
            continue
        q = min_fac(m, primes)
        if miller_rabin(q - 2):
            continue
        if q < 107:
            continue
        leftover.append((p, q, m // q, factors(m, primes)))

    print(f"leftover remaining p < {n}: {len(leftover)}")

    plans = [
        ("5/7", [5], [7]),
        ("5,11 / 7,13", [5, 11], [7, 13]),
        ("5,11,17,23 / 7,13,19,25", [5, 11, 17, 23], [7, 13, 19, 25]),
        ("5..47 / 7..43", [5, 11, 17, 23, 29, 41, 47], [7, 13, 19, 25, 31, 37, 43]),
    ]
    for name, k2, k1 in plans:
        c = sum(1 for p, _q, _s, facs in leftover if covered_by_k(p, facs, k2, k1))
        print(f"covered by {name}: {c} / {len(leftover)}")
        if c < len(leftover) and name.startswith("5,11,17,23"):
            miss = [
                (p, q, s, facs)
                for p, q, s, facs in leftover
                if not covered_by_k(p, facs, k2, k1)
            ]
            print("missed by 5..23 / 7..25:", miss)

    uncovered = []
    kstats = []
    for p, q, s, facs in leftover:
        hit = None
        for r in facs:
            found = first_injector(r, (p - 2) // r)
            if found is not None:
                hit = (r, found[0], found[1])
                break
        if hit is None:
            uncovered.append((p, q, s, facs))
        else:
            kstats.append(hit[1])

    print(f"no injector in the McEachen window k <= (p-2)/r: {len(uncovered)}")
    if kstats:
        print(
            "covering k min/max/mean:",
            min(kstats),
            max(kstats),
            f"{sum(kstats) / len(kstats):.3f}",
        )
    if uncovered:
        print("first uncovered:")
        for row in uncovered[:20]:
            print(row)

    fails = []
    worst = (0, 0, 0)
    for q in primes:
        if q < 5 or q >= 50000:
            continue
        found = first_injector(q, q + 2)
        if found is None:
            fails.append(q)
        elif found[0] > worst[0]:
            worst = (found[0], q, found[1])
    print("square-window failures for primes q < 50000:", fails)
    print("worst first k in that range:", worst)


if __name__ == "__main__":
    main()
