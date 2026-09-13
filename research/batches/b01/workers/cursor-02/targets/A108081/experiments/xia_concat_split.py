#!/usr/bin/env python3
"""Does every Xia word with ≥2 zeros split as a concatenation of two Xia words?"""
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
                    nxt.add(u + R(v))
        words[n] = nxt
    return words


def right_parses(w: Word, by_len: dict[int, set[Word]]):
    n = len(w)
    out = []
    for i in range(1, n):
        pre, suf = w[:i], w[i:]
        vv = L(suf)
        if pre in by_len[i] and vv in by_len[n - i]:
            out.append((pre, vv))
    return out


def xia_concat_splits(w: Word, by_len) -> list[int]:
    n = len(w)
    return [
        m
        for m in range(1, n)
        if w[:m] in by_len[m] and w[m:] in by_len[n - m]
    ]


def main() -> None:
    max_n = 7
    words = enumerate_x(max_n)
    P = {n: {w for w in words[n] if w.count(0) == 1} for n in range(1, max_n + 1)}
    Right = {n: {w for w in P[n] if w[0] == 0} for n in range(1, max_n + 1)}

    print("=== Xia words with ≥2 zeros: concat split? ===")
    for n in range(2, max_n + 1):
        multi = [w for w in words[n] if w.count(0) >= 2]
        nosplit = [w for w in multi if not xia_concat_splits(w, words)]
        print(
            f" n={n}: multi0={len(multi)} nosplit={len(nosplit)} "
            f"e.g.={nosplit[:3]}"
        )

    print("=== concat splits of shortest remainder of start-0 PWords ===")
    for n in range(2, max_n + 1):
        split_p = 0
        split_nonp = 0
        for w in Right[n]:
            rp = right_parses(w, words)
            mlen = min(len(v) for _, v in rp)
            u, v = next((u, v) for u, v in rp if len(v) == mlen)
            splits = xia_concat_splits(v, words)
            if splits:
                if v in P[len(v)]:
                    split_p += 1
                else:
                    split_nonp += 1
        print(f" n={n}: shortest_remainder_has_concat_split P={split_p} nonP={split_nonp}")

    print("=== if remainder has concat split m, is that a shorter parse of w? ===")
    for n in range(2, max_n + 1):
        ok = 0
        fail = 0
        shorter = 0
        not_shorter = 0
        for w in Right[n]:
            rp = right_parses(w, words)
            mlen = min(len(v) for _, v in rp)
            for u, v in rp:
                splits = xia_concat_splits(v, words)
                for m in splits:
                    take, drop = v[:m], v[m:]
                    left = u + R(drop)
                    recon = left + R(take)
                    left_x = left in words.get(len(left), set())
                    if recon == w and left_x and take in words[len(take)]:
                        ok += 1
                        if m < len(v):
                            shorter += 1
                        else:
                            not_shorter += 1
                    else:
                        fail += 1
        print(
            f" n={n}: ok={ok} fail={fail} shorter_remainder={shorter} "
            f"not_shorter={not_shorter}"
        )

    print("=== YWord shortest remainder in P? ===")
    Y: dict[int, set[Word]] = {1: {(0,)}}
    for n in range(2, max_n + 1):
        nxt = set()
        for i in range(1, n):
            for u in Y[i]:
                for v in words[n - i]:
                    nxt.add(u + R(v))
        Y[n] = nxt
    for n in range(2, max_n + 1):
        notp = 0
        noparse = 0
        for w in Y[n]:
            rp = right_parses(w, words)
            if not rp:
                noparse += 1
                continue
            mlen = min(len(v) for _, v in rp)
            u, v = next((u, v) for u, v in rp if len(v) == mlen)
            if v not in P[len(v)]:
                notp += 1
        print(f" n={n}: |Y|={len(Y[n])} shortest_notP={notp} noparse={noparse}")

    print("=== start-0 PWord: longest proper Xia prefix vs shortest remainder left ===")
    for n in range(2, max_n + 1):
        mismatch = 0
        for w in Right[n]:
            xia_prefs = [k for k in range(1, n) if w[:k] in words[k]]
            rp = right_parses(w, words)
            mlen = min(len(v) for _, v in rp)
            u, v = next((u, v) for u, v in rp if len(v) == mlen)
            longest = max(xia_prefs)
            if longest != len(u):
                mismatch += 1
        print(f" n={n}: longest_xia_prefix_ne_shortest_left={mismatch}")


if __name__ == "__main__":
    main()
