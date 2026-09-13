#!/usr/bin/env python3
"""Remaining concat_split case: last=1, dropLast not Xia, shortest left is PWord."""
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
            for u in words[i]:
                lu = L(u)
                for v in words[n - i]:
                    nxt.add(lu + v)
                    nxt.add(u + R(v))
        words[n] = nxt
    return words


def right_parses(w, words):
    n = len(w)
    return [
        (w[:i], L(w[i:]))
        for i in range(1, n)
        if w[:i] in words[i] and L(w[i:]) in words[n - i]
    ]


def concat_splits(w, words):
    n = len(w)
    return [m for m in range(1, n) if w[:m] in words[m] and w[m:] in words[n - m]]


def main() -> None:
    max_n = 7
    words = enumerate_x(max_n)
    for n in range(2, max_n + 1):
        rem = []
        for w in words[n]:
            if w.count(0) < 2:
                continue
            if w[-1] != 1:
                continue
            if w[:-1] in words[n - 1]:
                continue
            rp = right_parses(w, words)
            if not rp:
                rem.append(("noparse", w))
                continue
            m = min(len(v) for _, v in rp)
            u, v = next((u, v) for u, v in rp if len(v) == m)
            if u.count(0) != 1:
                continue
            rem.append((w, u, v, concat_splits(w, words)))
        print(f" n={n}: remaining={len(rem)}")
        for r in rem[:6]:
            print("  ", r)


if __name__ == "__main__":
    main()
