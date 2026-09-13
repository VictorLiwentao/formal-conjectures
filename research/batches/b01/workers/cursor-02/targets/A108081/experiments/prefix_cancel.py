#!/usr/bin/env python3
"""Cancellation when the middle is a prefix of an I-word or suffix of a Y-word."""
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


def is_pword(w):
    return w.count(0) == 1


def main() -> None:
    max_n = 8
    words = enumerate_x(max_n)
    I, Left, Right, Y = {}, {}, {}, {}
    for n in range(1, max_n + 1):
        I[n] = {w for w in words[n] if not parses(w, words)[1]}
        Left[n] = {w for w in words[n] if is_pword(w) and w[-1] == 0}
        Right[n] = {w for w in words[n] if is_pword(w) and w[0] == 0}
    Y[1] = {(0,)}
    for n in range(2, max_n + 1):
        s = set()
        for i in range(1, n):
            for u in Y[i]:
                for v in words[n - i]:
                    s.add(u + R(v))
        Y[n] = s

    prefixes_I = set()
    for n in range(1, max_n + 1):
        for v in I[n]:
            for i in range(len(v) + 1):
                prefixes_I.add(v[:i])

    print("=== L(Left)++b Xia and b prefix of some I ⇒ b Xia ===")
    for n in range(2, max_n + 1):
        fail = 0
        ok = 0
        for k in range(1, n):
            for p in Left[k]:
                lu = L(p)
                for w in words[n]:
                    if w[:k] == lu:
                        b = w[k:]
                        if b not in prefixes_I:
                            continue
                        if b in words.get(n - k, set()) or b == ():
                            ok += 1
                        else:
                            fail += 1
                            if fail <= 8:
                                print("  fail p", p, "b", b, "w", w)
        print(f" n={n} ok={ok} fail={fail}")

    suffixes_Y = set()
    for n in range(1, max_n + 1):
        for y in Y[n]:
            for i in range(len(y) + 1):
                suffixes_Y.add(y[i:])

    print("=== s ++ R(Right) Xia and s suffix of some Y ⇒ s Xia ===")
    for n in range(2, max_n + 1):
        fail = 0
        ok = 0
        for k in range(1, n):
            for t in Right[k]:
                rt = R(t)
                for w in words[n]:
                    if w[-k:] == rt:
                        s = w[:-k]
                        if s not in suffixes_Y:
                            continue
                        if s in words.get(n - k, set()) or s == ():
                            ok += 1
                        else:
                            fail += 1
                            if fail <= 8:
                                print("  fail s", s, "t", t, "w", w)
        print(f" n={n} ok={ok} fail={fail}")

    print("\n=== L(p)++v I for all I v, as a set of p (stability) ===")
    P = {n: {w for w in words[n] if is_pword(w)} for n in range(1, max_n + 1)}
    for k in range(1, max_n):
        sets = []
        for n in range(k + 1, max_n + 1):
            good_by_v = []
            for v in I[n - k]:
                good = frozenset(p for p in P[k] if L(p) + v in I[n])
                good_by_v.append(good)
            if good_by_v:
                all_eq = all(g == good_by_v[0] for g in good_by_v)
                print(
                    f" k={k} n={n} |G|={len(good_by_v[0])} all_v_same={all_eq} "
                    f"G==G_[0]={good_by_v[0]==frozenset(p for p in P[k] if L(p)+(0,) in I[k+1])}"
                )


if __name__ == "__main__":
    main()
