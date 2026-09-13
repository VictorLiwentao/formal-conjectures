#!/usr/bin/env python3
"""Inspect candidate right-parse prefixes of L(s++[1])++[0] for PWords s."""
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
    max_n = 7
    words = enumerate_x(max_n)
    P = {}
    I = {}
    for n in range(1, max_n + 1):
        P[n] = {w for w in words[n] if w.count(0) == 1}
        I[n] = {w for w in words[n] if not parses(w, words)[1]}

    hard = 0
    for k in range(1, max_n):
        for s in P[k]:
            w = L(s + (1,)) + (0,)
            n = len(w)
            for i in range(3, n):
                pre = w[:i]
                last = pre[-1]
                if last not in (0, 1):
                    continue
                inx = pre in words[i]
                rem = w[i:]
                q = L(rem)
                qxia = q in words[len(q)]
                if inx:
                    hard += 1
                    print("XIA PREFIX", "s", s, "w", w, "pre", pre, "q", q, "qxia", qxia)
                elif last in (0, 1):
                    pass
    print("xia_prefix_len_ge_3", hard)
    print("all L(s++[1])++[0] in I?", all(
        L(s + (1,)) + (0,) in I[k + 2] for k in range(1, max_n - 1) for s in P[k]
    ))


if __name__ == "__main__":
    main()
