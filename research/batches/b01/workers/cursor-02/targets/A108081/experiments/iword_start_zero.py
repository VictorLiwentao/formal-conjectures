#!/usr/bin/env python3
"""Do I-words of length >= 2 ever start with 0?"""
from __future__ import annotations

Word = tuple[int, ...]


def L(w: Word) -> Word:
    return tuple(x - 1 for x in reversed(w))


def R(w: Word) -> Word:
    return tuple(x + 1 for x in reversed(w))


def enumerate_x(max_n: int) -> dict[int, set[Word]]:
    words: dict[int, set[Word]] = {1: {(0,)}}
    for n in range(2, max_n + 1):
        nxt: set[Word] = set()
        for i in range(1, n):
            j = n - i
            for u in words[i]:
                lu = L(u)
                for v in words[j]:
                    nxt.add(lu + v)
            for u in words[i]:
                for v in words[j]:
                    nxt.add(u + R(v))
        words[n] = nxt
    return words


def parses(w, by_len):
    left, right = [], []
    n = len(w)
    for i in range(1, n):
        pre, suf = w[:i], w[i:]
        u = R(pre)
        if u in by_len[i] and suf in by_len[n - i]:
            left.append((u, suf))
        v = L(suf)
        if pre in by_len[i] and v in by_len[n - i]:
            right.append((pre, v))
    return left, right


def main() -> None:
    max_n = 8
    words = enumerate_x(max_n)
    for n in range(1, max_n + 1):
        I = {w for w in words[n] if not parses(w, words)[1]}
        start0 = {w for w in I if w[0] == 0}
        start00 = {w for w in words[n] if w[0] == 0 and n >= 2 and w[1] == 0}
        I00 = start0 & {w for w in I if n >= 2 and w[1] == 0}
        print(
            f"n={n} |I|={len(I)} I_start0={sorted(start0)} "
            f"|X_00|={len(start00)} I_00={sorted(I00)}"
        )
        if n <= 5:
            print("  X_00", sorted(start00))


if __name__ == "__main__":
    main()
