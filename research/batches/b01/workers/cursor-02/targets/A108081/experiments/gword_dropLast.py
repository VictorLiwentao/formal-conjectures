#!/usr/bin/env python3
"""Test G = LeftWords ∪ {s ++ [1] | s in P}, and dropLast-Xia among last=1 PWords."""
from __future__ import annotations

from math import comb

Word = tuple[int, ...]


def L(w: Word) -> Word:
    return tuple(x - 1 for x in reversed(w))


def R(w: Word) -> Word:
    return tuple(x + 1 for x in reversed(w))


def catalan(n: int) -> int:
    return comb(2 * n, n) // (n + 1)


def q(k: int) -> int:
    return 1 if k == 1 else 2 * catalan(k - 1)


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
    I, P, Left = {}, {}, {}
    for n in range(1, max_n + 1):
        I[n] = {w for w in words[n] if not parses(w, words)[1]}
        P[n] = {w for w in words[n] if w.count(0) == 1}
        Left[n] = {w for w in P[n] if w[-1] == 0}

    fail = 0
    for k in range(1, max_n):
        G0 = {p for p in P[k] if L(p) + (0,) in I[k + 1]}
        pred = set(Left[k])
        if k >= 2:
            pred |= {s + (1,) for s in P[k - 1]}
        dropLast_xia = {p for p in P[k] if p[-1] == 1 and p[:-1] in words[k - 1]}
        dropLast_p = {p for p in P[k] if p[-1] == 1 and p[:-1] in P[k - 1]}
        print(
            f"k={k} |G|={len(G0)} q={q(k)} |pred|={len(pred)} "
            f"|dropLast_xia|={len(dropLast_xia)} |dropLast_P|={len(dropLast_p)}"
        )
        if G0 != pred:
            fail += 1
            print("  only G", sorted(G0 - pred))
            print("  only pred", sorted(pred - G0))
        extra = G0 - Left[k]
        if extra != dropLast_xia:
            fail += 1
            print("  extra vs dropLast_xia", extra.symmetric_difference(dropLast_xia))
        if extra != dropLast_p:
            fail += 1
            print("  extra vs dropLast_P", extra.symmetric_difference(dropLast_p))
        # stability vs all I remainders
        for n in range(k + 1, max_n + 1):
            Gv = {p for p in P[k] if all(L(p) + v in I[n] for v in I[n - k])}
            if Gv != G0:
                fail += 1
                print("  stability fail", k, n)
    print("fail", fail)


if __name__ == "__main__":
    main()
