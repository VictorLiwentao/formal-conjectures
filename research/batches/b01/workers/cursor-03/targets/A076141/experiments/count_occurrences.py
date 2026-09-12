#!/usr/bin/env python3
"""Deterministic checks of the frozen A076141 counting convention.

These checks are not a resolution of the conjecture. They only compare the
Lean counting convention (MSB-first binary, overlapping infixes, zero as [0])
against the OEIS data and the structural constraints used in the statement audit.
"""

from __future__ import annotations

OEIS_PREFIX = [
    1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0,
]


def binary_pattern(n: int) -> str:
    return "0" if n == 0 else bin(n)[2:]


def a(n: int) -> int:
    pat = binary_pattern(n)
    tgt = binary_pattern(n * n)
    return sum(tgt[i : i + len(pat)] == pat for i in range(len(tgt) - len(pat) + 1))


def match_shifts(n: int) -> list[int]:
    if n == 0:
        return [0]
    k = n.bit_length()
    t = n * n
    L = t.bit_length()
    mask = (1 << k) - 1
    return [e for e in range(L - k + 1) if ((t >> e) & mask) == n]


def main() -> None:
    mismatches = [n for n, expected in enumerate(OEIS_PREFIX) if a(n) != expected]
    print(f"oeis_prefix_len={len(OEIS_PREFIX)}")
    print(f"oeis_prefix_mismatches={mismatches}")
    print(f"a0={a(0)} a1={a(1)} a2={a(2)} a3={a(3)} a4={a(4)} a5={a(5)} a27={a(27)}")
    print(f"a145={a(145)} a5={a(5)} a29={a(29)}")

    ge2 = [n for n in range(0, 200_001) if a(n) >= 2]
    print(f"a_ge2_upto_2e5={ge2}")
    print(f"max_a_upto_2e5={max(a(n) for n in range(0, 200_001))}")

    # Overlap convention: tails/SearchAll count every start, including overlaps.
    # The pattern 11 in 111 has two overlapping starts.
    print(f"overlap_demo_11_in_111={sum(s == '11' for s in ('111'[i:i+2] for i in range(2)))}")

    # Powers of two and all-ones.
    pow2 = [2**k for k in range(0, 20)]
    print("powers_of_two", [(n, a(n), match_shifts(n)) for n in pow2])
    all_ones = [2**k - 1 for k in range(1, 16)]
    print("all_ones", [(n, a(n)) for n in all_ones])

    # Suffix impossibility for n >= 2: n^2 % 2^k == n.
    suffix = []
    for n in range(2, 5000):
        k = n.bit_length()
        if (n * n) % (1 << k) == n:
            suffix.append(n)
    print(f"suffix_matches_n_ge2_lt5000={suffix}")


if __name__ == "__main__":
    main()
