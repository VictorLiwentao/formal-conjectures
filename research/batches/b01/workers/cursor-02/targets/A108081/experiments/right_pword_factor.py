#!/usr/bin/env python3
"""Factorization experiments for start-with-0 P-words (Right_n)."""
from __future__ import annotations

from math import comb

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


def catalan(n: int) -> int:
    return comb(2 * n, n) // (n + 1)


def right_parses(w: Word, by_len: dict[int, set[Word]]) -> list[tuple[Word, Word]]:
    n = len(w)
    out = []
    for i in range(1, n):
        pre, suf = w[:i], w[i:]
        vv = L(suf)
        if pre in by_len[i] and vv in by_len[n - i]:
            out.append((pre, vv))
    return out


def main() -> None:
    max_n = 7
    words = enumerate_x(max_n)
    P = {n: {w for w in words[n] if w.count(0) == 1} for n in range(1, max_n + 1)}
    Right = {n: {w for w in P[n] if w[0] == 0} for n in range(1, max_n + 1)}

    print("=== |Right_n| vs C_{n-1} ===")
    for n in range(1, max_n + 1):
        print(f" n={n}: |Right|={len(Right[n])} C_{n-1}={catalan(n - 1)}")

    print("=== u ++ R(v) on Right_i x Right_j ===")
    for n in range(1, max_n + 1):
        built: set[Word] = set()
        extra = []
        clash = 0
        for i in range(1, n):
            j = n - i
            for u in Right[i]:
                for v in Right[j]:
                    w = u + R(v)
                    if w in Right[n]:
                        if w in built:
                            clash += 1
                        built.add(w)
                    else:
                        extra.append((u, v, w))
        missing = Right[n] - built
        print(
            f" n={n}: built={len(built)} |Right|={len(Right[n])} "
            f"missing={len(missing)} extra={len(extra)} clash={clash}"
        )
        if missing:
            print("  miss", list(missing)[:3])
        if extra:
            print("  extra", extra[:2])

    print("=== shortest remainder of start-0 P-words ===")
    for n in range(2, max_n + 1):
        stats = {
            "notP": 0,
            "last0": 0,
            "last1": 0,
            "zeros_ge2": 0,
            "neg1": 0,
            "head_ne0": 0,
        }
        examples = []
        for w in Right[n]:
            rp = right_parses(w, words)
            m = min(len(v) for _, v in rp)
            hits = [(u, v) for u, v in rp if len(v) == m]
            assert len(hits) == 1
            u, v = hits[0]
            if v.count(-1):
                stats["neg1"] += 1
            if v[0] != 0:
                stats["head_ne0"] += 1
            if v[-1] == 0:
                stats["last0"] += 1
            if v[-1] == 1:
                stats["last1"] += 1
            if v.count(0) != 1:
                stats["zeros_ge2"] += 1
            if v not in P[len(v)]:
                stats["notP"] += 1
                if len(examples) < 3:
                    examples.append((w, u, v, rp))
        print(f" n={n}: {stats} examples_notP={examples[:1]}")

    print("=== extra (non-shortest) remainders: last letter, zeros, second-zero split ===")
    for n in range(2, max_n + 1):
        extra_last0 = 0
        extra_p = 0
        split_ok = 0
        split_fail = 0
        fail_ex = []
        for w in Right[n]:
            rp = right_parses(w, words)
            m = min(len(v) for _, v in rp)
            for u, v in rp:
                if len(v) == m:
                    continue
                if v[-1] == 0:
                    extra_last0 += 1
                if v in P[len(v)]:
                    extra_p += 1
                zeros = [i for i, x in enumerate(v) if x == 0]
                if len(zeros) < 2:
                    split_fail += 1
                    fail_ex.append(("few0", w, u, v))
                    continue
                k = zeros[1]
                take, drop = v[:k], v[k:]
                left = u + R(drop)
                if (
                    take in words[len(take)]
                    and drop in words[len(drop)]
                    and left in words[len(left)]
                    and w == left + R(take)
                ):
                    split_ok += 1
                else:
                    split_fail += 1
                    if len(fail_ex) < 3:
                        fail_ex.append(
                            (
                                "split",
                                w,
                                u,
                                v,
                                take,
                                drop,
                                take in words.get(len(take), set()),
                                drop in words.get(len(drop), set()),
                                left in words.get(len(left), set()),
                            )
                        )
        print(
            f" n={n}: extra_last0={extra_last0} extra_is_P={extra_p} "
            f"second0_split_ok={split_ok} fail={split_fail} fail_ex={fail_ex[:1]}"
        )

    print("=== last(v)=0 for ANY remainder of start-0 P-word? dropLast Xia? ===")
    for n in range(2, max_n + 1):
        last0 = 0
        droplast_x = 0
        append1_parse = 0
        for w in Right[n]:
            rp = right_parses(w, words)
            for u, v in rp:
                if v[-1] != 0:
                    continue
                last0 += 1
                init = v[:-1]
                if init in words.get(len(init), set()):
                    droplast_x += 1
                u1 = u + (1,)
                rest = L(w[len(u) + 1 :]) if len(u) + 1 < n else None
                if (
                    len(u) + 1 < n
                    and u1 in words.get(len(u1), set())
                    and rest in words.get(n - len(u) - 1, set())
                ):
                    append1_parse += 1
        print(
            f" n={n}: remainders_last0={last0} droplast_in_X={droplast_x} "
            f"u++[1]_is_parse={append1_parse}"
        )

    print("=== YWord vs nonnegative start-0 Xia ===")
    # Y-words: smallest containing (0,) closed under u ++ R(v) for v in X
    Y: dict[int, set[Word]] = {1: {(0,)}}
    for n in range(2, max_n + 1):
        nxt = set()
        for i in range(1, n):
            for u in Y[i]:
                for v in words[n - i]:
                    nxt.add(u + R(v))
        Y[n] = nxt
    for n in range(1, max_n + 1):
        nn = {w for w in words[n] if w[0] == 0 and -1 not in w}
        start0 = {w for w in words[n] if w[0] == 0}
        print(
            f" n={n}: |Y|={len(Y[n])} nonnegative_start0={len(nn)} "
            f"Y==nn={Y[n]==nn} start0={len(start0)} Y_has_neg1={any(-1 in w for w in Y[n])}"
        )

    print("=== shortest remainder last letter; u ++ [1] when last(v)=0 ===")
    for n in range(2, max_n + 1):
        short_last0 = 0
        for w in Right[n]:
            rp = right_parses(w, words)
            m = min(len(v) for _, v in rp)
            u, v = next((u, v) for u, v in rp if len(v) == m)
            if v[-1] == 0:
                short_last0 += 1
                print("  short last0", w, u, v)
        print(f" n={n}: shortest_last0={short_last0}")


if __name__ == "__main__":
    main()
