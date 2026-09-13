#!/usr/bin/env python3
"""Catalan first-peel family P_k for Y-words."""
from __future__ import annotations

from collections import Counter
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


def right_parses(w: Word, by_len):
    n = len(w)
    out = []
    for i in range(1, n):
        pre, suf = w[:i], w[i:]
        v = L(suf)
        if pre in by_len[i] and v in by_len[n - i]:
            out.append((pre, v))
    return out


def shortest_right(w, by_len):
    rp = right_parses(w, by_len)
    if not rp:
        return None
    m = min(len(v) for _, v in rp)
    hits = [(u, v) for u, v in rp if len(v) == m]
    assert len(hits) == 1
    return hits[0]


def catalan(n: int) -> int:
    return comb(2 * n, n) // (n + 1)


def endpoint(w: Word) -> str:
    return {(0, 0): "A", (0, 1): "B", (-1, 0): "C", (-1, 1): "D"}[(w[0], w[-1])]


def main() -> None:
    max_n = 7
    words = enumerate_x(max_n)
    by_len = words

    def P(k: int) -> set[Word]:
        pk = set()
        for v in words[k]:
            w = (0,) + R(v)
            hit = shortest_right(w, by_len)
            if hit is not None and hit[1] == v:
                pk.add(v)
        return pk

    print("=== |P_k| vs Catalan ===")
    for k in range(1, max_n):
        pk = P(k)
        print(
            f" k={k}: |P|={len(pk)} C_k={catalan(k)} C_{k-1}={catalan(k-1)} "
            f"|X|={len(words[k])}"
        )
        if k <= 4:
            for v in sorted(pk):
                print(f"   P {v} ep={endpoint(v)}")
            print("  not P:")
            for v in sorted(words[k] - pk):
                w = (0,) + R(v)
                hit = shortest_right(w, by_len)
                print(f"   {v} ep={endpoint(v)} short={hit}")

    print("=== is P_k uniform for every Y-prefix u? ===")

    def Yset(n):
        ys = set()
        for w in words[n]:
            cur = w
            ok = True
            while True:
                hit = shortest_right(cur, by_len)
                if hit is None:
                    ok = cur == (0,)
                    break
                cur = hit[0]
            if ok:
                ys.add(w)
        return ys

    for n in range(1, max_n + 1):
        # rebuild Y via greedy to [0]
        pass
    Y = {n: Yset(n) for n in range(1, max_n + 1)}

    for m in range(1, max_n):
        # for each u in Y_m, allowed v of each length
        mismatch = 0
        sizes = Counter()
        p_ref = {k: P(k) for k in range(1, max_n - m + 1)}
        for u in Y[m]:
            for k in range(1, max_n - m + 1):
                allowed = set()
                for v in words[k]:
                    w = u + R(v)
                    if w not in words[m + k]:
                        continue
                    hit = shortest_right(w, by_len)
                    if hit is not None and hit[1] == v:
                        allowed.add(v)
                if allowed != p_ref[k]:
                    mismatch += 1
                    if mismatch <= 3:
                        print(
                            f" mismatch u={u} k={k} |all|={len(allowed)} "
                            f"|P|={len(p_ref[k])} onlyP={p_ref[k]-allowed} "
                            f"extra={allowed-p_ref[k]}"
                        )
                sizes[(m, k, len(allowed))] += 1
        print(f" Y_m={m}: mismatches vs P_k={mismatch}")

    print("=== first-peel length hist of Y vs C_k |Y_{n-k}| ===")
    for n in range(2, max_n + 1):
        hist = Counter()
        for y in Y[n]:
            hit = shortest_right(y, by_len)
            hist[len(hit[1])] += 1
        pred = {k: catalan(k) * len(Y[n - k]) for k in range(1, n)}
        print(f" n={n}: hist={dict(sorted(hist.items()))} pred={pred} match={hist == Counter(pred)}")

    print("=== P_k by endpoint / max / min / zeros ===")
    for k in range(1, max_n):
        pk = P(k)
        print(
            f" k={k}: ep {Counter(endpoint(v) for v in pk)} "
            f"max {Counter(max(v) for v in pk)} "
            f"min {Counter(min(v) for v in pk)} "
            f"zeros {Counter(v.count(0) for v in pk)} "
            f"first {Counter(v[0] for v in pk)} last {Counter(v[-1] for v in pk)}"
        )

    print("=== recursive structure of P: P = L(X)++P? or X++R(P)? ===")
    # Catalan: binary tree = root + two Catalan, or first-return Dyck
    for k in range(2, min(6, max_n)):
        pk = P(k)
        # unique right parse of v itself?
        both = 0
        uniqR = 0
        noR = 0
        for v in pk:
            rp = right_parses(v, by_len)
            if not rp:
                noR += 1
            elif len(rp) == 1:
                uniqR += 1
            lp = []
            n = len(v)
            for i in range(1, n):
                pre, suf = v[:i], v[i:]
                u = R(pre)
                if u in by_len[i] and suf in by_len[n - i]:
                    lp.append((u, suf))
            if lp and rp:
                both += 1
        print(f" P_{k}: noR={noR} uniqR={uniqR} |P|={len(pk)} bothLR_exist={both}")

    print("=== try: v in P iff 0 is not in v[1:-1] or other simple ===")
    for k in range(1, max_n):
        pk = P(k)
        tests = {
            "no_internal_0": lambda v: all(v[i] != 0 for i in range(1, k - 1)),
            "starts_neg_or_len1": lambda v: k == 1 or v[0] == -1,
            "not_A": lambda v: not (v[0] == 0 and v[-1] == 0),
            "has_L_or_len1": lambda v: k == 1 or v[0] == -1 or v[-1] == 1,
            "max_le_1": lambda v: max(v) <= 1,
            "sum_ge_0": lambda v: sum(v) >= 0,
            "first_last_not_A_and_not_internal_pos_0": lambda v: endpoint(v) != "A",
        }
        for name, fn in tests.items():
            pred = {v for v in words[k] if fn(v)}
            if pred == pk:
                print(f"  MATCH k={k} {name}")
        # print size of not_A
        notA = {v for v in words[k] if endpoint(v) != "A"}
        print(f"  k={k} |notA|={len(notA)} |P|={len(pk)}")


if __name__ == "__main__":
    main()
