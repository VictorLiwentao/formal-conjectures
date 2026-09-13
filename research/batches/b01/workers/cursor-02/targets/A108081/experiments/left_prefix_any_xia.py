#!/usr/bin/env python3
"""Does L(Left)++b Xia and b a prefix of some Xia word imply b Xia?

The proved lemma uses only XWord v, not RIrreducible. Check whether that
stronger statement holds through n=8.
"""
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


def is_pword(w: Word) -> bool:
    return w.count(0) == 1


def main() -> None:
    max_n = 8
    words = enumerate_x(max_n)
    Left = {}
    for n in range(1, max_n + 1):
        Left[n] = {w for w in words[n] if is_pword(w) and w[-1] == 0}

    prefixes_X = set()
    for n in range(1, max_n + 1):
        for v in words[n]:
            for i in range(len(v) + 1):
                prefixes_X.add(v[:i])

    print("=== L(Left)++b Xia and b prefix of some Xia => b Xia ===")
    for n in range(2, max_n + 1):
        fail = 0
        ok = 0
        for k in range(1, n):
            for p in Left[k]:
                lu = L(p)
                for w in words[n]:
                    if w[:k] != lu:
                        continue
                    b = w[k:]
                    if b not in prefixes_X:
                        continue
                    if b in words.get(n - k, set()) or b == ():
                        ok += 1
                    else:
                        fail += 1
                        if fail <= 8:
                            print("  fail p", p, "b", b, "w", w)
        print(f" n={n} ok={ok} fail={fail}")


if __name__ == "__main__":
    main()
