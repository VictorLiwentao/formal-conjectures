#!/usr/bin/env python3
"""Per-remainder good PWord counts and Left-cancellation checks."""
from __future__ import annotations

from collections import Counter
from math import comb

Word = tuple[int, ...]


def L(w: Word) -> Word:
    return tuple(x - 1 for x in reversed(w))


def R(w: Word) -> Word:
    return tuple(x + 1 for x in reversed(w))


def catalan(n: int) -> int:
    return comb(2 * n, n) // (n + 1)


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


def parses(w: Word, by_len: dict[int, set[Word]]):
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


def is_pword(w: Word) -> bool:
    return w.count(0) == 1


def q(k: int) -> int:
    return 1 if k == 1 else 2 * catalan(k - 1)


def main() -> None:
    max_n = 8
    words = enumerate_x(max_n)
    I, P, Left, Right = {}, {}, {}, {}
    for n in range(1, max_n + 1):
        I[n] = {w for w in words[n] if not parses(w, words)[1]}
        P[n] = {w for w in words[n] if is_pword(w)}
        Right[n] = {w for w in P[n] if w[0] == 0}
        Left[n] = {w for w in P[n] if w[-1] == 0}

    print("=== cancellation: L(Left)++b Xia ⇒ b Xia? ===")
    for n in range(2, max_n + 1):
        fail = 0
        ok = 0
        for k in range(1, n):
            for p in Left[k]:
                for w in words[n]:
                    lu = L(p)
                    if w[:k] == lu:
                        b = w[k:]
                        if b in words[n - k]:
                            ok += 1
                        else:
                            fail += 1
                            if fail <= 3:
                                print("  fail", p, b, w)
        print(f" n={n} ok={ok} fail={fail}")

    print("\n=== cons-neg-one: [-1]++b Xia ⇒ b Xia? ===")
    for n in range(2, max_n + 1):
        fail = 0
        for w in words[n]:
            if w[0] == -1:
                b = w[1:]
                if b not in words[n - 1]:
                    fail += 1
                    if fail <= 5:
                        print("  fail", w, b, "b in X", b in words.get(n - 1, set()))
        print(f" n={n} start-1={sum(w[0]==-1 for w in words[n])} tail-not-X={fail}")

    print("\n=== per v, number of good p in P_k ===")
    for n in range(2, max_n + 1):
        varying = []
        for k in range(1, n):
            counts = []
            for v in I[n - k]:
                good = [p for p in P[k] if L(p) + v in I[n]]
                counts.append(len(good))
            uniq = Counter(counts)
            qk = q(k)
            print(f" n={n} k={k} q={qk} |P|={len(P[k])} |I_rem|={len(I[n-k])} counts={dict(uniq)}")
            if any(c != qk for c in counts):
                varying.append((k, uniq))

    print("\n=== I-words starting with -1: is tail I / X / Z? ===")
    for n in range(2, max_n + 1):
        c = Counter()
        for w in I[n]:
            if w[0] == -1:
                b = w[1:]
                c[
                    "I" if b in I[n - 1] else
                    "X" if b in words[n - 1] else
                    "notX"
                ] += 1
        print(f" n={n} start-1 I-words tail={dict(c)}")

    print("\n=== good p for each v, classified L/R/M ===")
    for n in range(2, min(max_n, 6) + 1):
        for k in range(1, n):
            print(f" -- n={n} k={k} --")
            for v in sorted(I[n - k]):
                goods = []
                for p in sorted(P[k]):
                    w = L(p) + v
                    if w in I[n]:
                        kind = "L" if p in Left[k] else "R" if p in Right[k] else "M"
                        goods.append((kind, p))
                print(f"  v={v} good={goods}")


if __name__ == "__main__":
    main()
