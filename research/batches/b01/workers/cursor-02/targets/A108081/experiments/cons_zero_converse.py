#!/usr/bin/env python3
"""If 0::w is Xia and w starts with -1, is w Xia?"""
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


def main() -> None:
    max_n = 8
    words = enumerate_x(max_n)
    fail = 0
    ok = 0
    for n in range(2, max_n + 1):
        for w0 in words[n]:
            if w0[0] != 0:
                continue
            w = w0[1:]
            if not w or w[0] != -1:
                continue
            if w in words[n - 1]:
                ok += 1
            else:
                fail += 1
                if fail <= 8:
                    print("fail", w0, "tail", w)
    print("ok", ok, "fail", fail)


if __name__ == "__main__":
    main()
