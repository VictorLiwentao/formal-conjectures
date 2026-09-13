#!/usr/bin/env python3
"""Test: s ++ R(t) Xia and t RightWord ⇒ s Xia."""
from __future__ import annotations

from math import comb

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


def is_pword(w: Word) -> bool:
    return w.count(0) == 1


def main() -> None:
    max_n = 8
    words = enumerate_x(max_n)
    Right = {}
    for n in range(1, max_n + 1):
        Right[n] = {w for w in words[n] if is_pword(w) and w[0] == 0}

    print("=== s ++ R(Right) Xia ⇒ s Xia ===")
    for n in range(2, max_n + 1):
        fail = 0
        ok = 0
        for k in range(1, n):
            for t in Right[k]:
                rt = R(t)
                for w in words[n]:
                    if w[-k:] == rt:
                        s = w[:-k]
                        if not s:
                            fail += 1
                            print("  empty s", w, t)
                            continue
                        if s in words[n - k]:
                            ok += 1
                        else:
                            fail += 1
                            if fail <= 6:
                                print("  fail s", s, "t", t, "w", w)
        print(f" n={n} ok={ok} fail={fail}")

    print("\n=== s ++ R(PWord) Xia ⇒ s Xia ===")
    P = {}
    for n in range(1, max_n + 1):
        P[n] = {w for w in words[n] if is_pword(w)}
    for n in range(2, max_n + 1):
        fail = 0
        ok = 0
        for k in range(1, n):
            for t in P[k]:
                rt = R(t)
                for w in words[n]:
                    if len(w) >= k and w[-k:] == rt:
                        s = w[:-k]
                        if not s:
                            continue
                        if s in words[n - k]:
                            ok += 1
                        else:
                            fail += 1
                            if fail <= 4:
                                print("  fail s", s, "t", t, "w", w)
        print(f" n={n} ok={ok} fail={fail}")


if __name__ == "__main__":
    main()
