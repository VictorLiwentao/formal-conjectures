#!/usr/bin/env python3
"""Can a Xia prefix have a longer shortest-left factor than the whole word?"""
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


def shortest_left(w, by_len):
    lp, _ = parses(w, by_len)
    if not lp:
        return None
    m = min(len(u) for u, _ in lp)
    hits = [(u, v) for u, v in lp if len(u) == m]
    return hits[0]


def main() -> None:
    max_n = 7
    words = enumerate_x(max_n)
    by = words
    longer = 0
    checked = 0
    for n in range(2, max_n + 1):
        for w in words[n]:
            sl = shortest_left(w, by)
            if sl is None:
                continue
            plen = len(sl[0])
            for m in range(plen + 1, n):
                u = w[:m]
                if u not in words[m]:
                    continue
                slu = shortest_left(u, by)
                if slu is None:
                    continue
                checked += 1
                if len(slu[0]) > plen:
                    longer += 1
                    if longer <= 8:
                        print("w", w, "slw", sl[0], "prefix", u, "slu", slu[0])
        print(f"n={n} longer={longer} checked={checked}")
    print("total longer", longer, "checked", checked)


if __name__ == "__main__":
    main()
