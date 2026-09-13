#!/usr/bin/env python3
"""Coverage of the paired 5/7 injectors on remaining McEachen primes.

Experimental only; not a Lean proof. Remaining means p ≡ 1 (mod 3), p-2
composite, lpf(p-2) ≥ 107, and that least factor is not a larger twin.
"""

from __future__ import annotations


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return n == 2 or n == 3
    d = 5
    while d * d <= n:
        if n % d == 0 or n % (d + 2) == 0:
            return False
        d += 6
    return True


def min_fac(n: int) -> int:
    if n % 2 == 0:
        return 2
    if n % 3 == 0:
        return 3
    d = 5
    while d * d <= n:
        if n % d == 0:
            return d
        if n % (d + 2) == 0:
            return d + 2
        d += 6
    return n


def is_larger_twin(q: int) -> bool:
    return q >= 13 and is_prime(q - 2)


def main() -> None:
    limit = 200000
    remaining = 0
    covered = 0
    by_kind = {
        "5q-2": 0,
        "7q-2": 0,
        "5s-2": 0,
        "7s-2": 0,
        "11q-2": 0,
        "13q-2": 0,
    }
    uncovered_examples = []
    for p in range(5, limit):
        if p % 3 != 1 or not is_prime(p):
            continue
        if is_prime(p - 2):
            continue
        q = min_fac(p - 2)
        if q < 107:
            continue
        if is_larger_twin(q):
            continue
        remaining += 1
        s = (p - 2) // q
        flags = {
            "5q-2": is_prime(5 * q - 2),
            "7q-2": is_prime(7 * q - 2),
            "5s-2": is_prime(5 * s - 2),
            "7s-2": is_prime(7 * s - 2),
            "11q-2": is_prime(11 * q - 2),
            "13q-2": is_prime(13 * q - 2),
        }
        paired = flags["5q-2"] or flags["7q-2"] or flags["5s-2"] or flags["7s-2"]
        extra = flags["11q-2"] or flags["13q-2"]
        if paired:
            covered += 1
        elif extra:
            pass
        elif len(uncovered_examples) < 15:
            uncovered_examples.append((p, q, s, q % 3, s % 3))
        for k, v in flags.items():
            if v:
                by_kind[k] += 1
    print(f"remaining McEachen primes p < {limit}: {remaining}")
    print(f"covered by 5q-2 or 7q-2 or 5s-2 or 7s-2: {covered}")
    print(f"uncovered by that pairing: {remaining - covered}")
    print("counts (a prime may hit several):", by_kind)
    print("first uncovered (p, q, s, q%3, s%3):")
    for row in uncovered_examples:
        print(row)


if __name__ == "__main__":
    main()
