#!/usr/bin/env python3
"""PWord prefix-cancellation: L(p)++b Xia, b prefix of some Xia word ⇒ b Xia."""
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
                for v in words[n - i]:
                    nxt.add(u + R(v))
        words[n] = nxt
    return words


def is_pword(w):
    return w.count(0) == 1


def main() -> None:
    max_n = 7
    words = enumerate_x(max_n)
    prefixes = set()
    for n in range(1, max_n + 1):
        for w in words[n]:
            for i in range(len(w) + 1):
                prefixes.add(w[:i])
    P = {}
    for n in range(1, max_n + 1):
        P[n] = {w for w in words[n] if is_pword(w)}
    for n in range(2, max_n + 1):
        fail = 0
        ok = 0
        for k in range(1, n):
            for p in P[k]:
                lu = L(p)
                for w in words[n]:
                    if w[:k] != lu:
                        continue
                    b = w[k:]
                    if b not in prefixes:
                        continue
                    if b in words.get(n - k, set()) or b == ():
                        ok += 1
                    else:
                        fail += 1
                        if fail <= 5:
                            print("fail p", p, "b", b, "w", w)
        print(f"n={n} ok={ok} fail={fail}")


if __name__ == "__main__":
    main()
