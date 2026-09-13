#!/usr/bin/env python3
"""Test G = {p in P | last==0 or penultimate <= 1}, and whether bad words
have a right parse of L(p)++[0] with left factor [0]."""
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
    I, P = {}, {}
    for n in range(1, max_n + 1):
        I[n] = {w for w in words[n] if not parses(w, words)[1]}
        P[n] = {w for w in words[n] if w.count(0) == 1}

    fail_char = 0
    fail_split = 0
    for k in range(2, max_n):
        G0 = {p for p in P[k] if L(p) + (0,) in I[k + 1]}
        pred = set()
        for p in P[k]:
            if p[-1] == 0 or p[-2] <= 1:
                pred.add(p)
        if G0 != pred:
            fail_char += 1
            print("char mismatch k", k, "only G", sorted(G0 - pred), "only pred", sorted(pred - G0))
        else:
            print(f"k={k} G==pred |G|={len(G0)}")
        for p in P[k] - G0:
            w = L(p) + (0,)
            _, rp = parses(w, words)
            has0 = any(u == (0,) for u, _ in rp)
            if not has0:
                fail_split += 1
                print("  no [0]-parse", p, "w", w, "rp", rp)
    print("char_fail", fail_char, "no_[0]_parse", fail_split)


if __name__ == "__main__":
    main()
