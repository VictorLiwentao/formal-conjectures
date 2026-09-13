#!/usr/bin/env python3
"""First-return / Wilf / height experiments for right-irreducible Xia words.

Not a proof. Exhaustive through n = 8.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import product
from math import comb

Word = tuple[int, ...]


def L(w: Word) -> Word:
    return tuple(x - 1 for x in reversed(w))


def R(w: Word) -> Word:
    return tuple(x + 1 for x in reversed(w))


def rho(w: Word) -> Word:
    return tuple(-x for x in reversed(w))


def catalan(n: int) -> int:
    return comb(2 * n, n) // (n + 1)


def H(m: int) -> int:
    if m == 0:
        return 1
    return comb(2 * m - 1, m - 1)


def a081696(n: int) -> int:
    # Munarini
    return sum(
        comb(2 * n - k, n + k) * (3 * k + 1) // (n + k + 1) for k in range(n + 1)
    )


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


def parses(
    w: Word, by_len: dict[int, set[Word]]
) -> tuple[list[tuple[Word, Word]], list[tuple[Word, Word]]]:
    left: list[tuple[Word, Word]] = []
    right: list[tuple[Word, Word]] = []
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


def shortest_left(w: Word, by_len: dict[int, set[Word]]) -> tuple[Word, Word] | None:
    lp, _ = parses(w, by_len)
    if not lp:
        return None
    m = min(len(u) for u, _ in lp)
    hits = [(u, v) for u, v in lp if len(u) == m]
    assert len(hits) == 1, (w, hits)
    return hits[0]


def shortest_right(w: Word, by_len: dict[int, set[Word]]) -> tuple[Word, Word] | None:
    _, rp = parses(w, by_len)
    if not rp:
        return None
    m = min(len(v) for _, v in rp)
    hits = [(u, v) for u, v in rp if len(v) == m]
    assert len(hits) == 1, (w, hits)
    return hits[0]


def compositions(n: int) -> list[tuple[int, ...]]:
    out: list[tuple[int, ...]] = []

    def rec(remain: int, acc: list[int]) -> None:
        if remain == 0:
            out.append(tuple(acc))
            return
        for k in range(1, remain + 1):
            acc.append(k)
            rec(remain - k, acc)
            acc.pop()

    rec(n, [])
    return out


def irreducible_pairs(n: int) -> list[tuple[tuple[int, ...], tuple[int, ...]]]:
    pairs: list[tuple[tuple[int, ...], tuple[int, ...]]] = []
    for k in range(1, n + 1):
        parts = [c for c in compositions(n) if len(c) == k]
        for a, b in product(parts, repeat=2):
            pa = [sum(a[: j + 1]) for j in range(k - 1)]
            pb = [sum(b[: j + 1]) for j in range(k - 1)]
            if all(x != y for x, y in zip(pa, pb)):
                pairs.append((a, b))
    return pairs


def zero_positions(w: Word) -> tuple[int, ...]:
    return tuple(i for i, x in enumerate(w) if x == 0)


def steps(w: Word) -> tuple[int, ...]:
    return tuple(w[i + 1] - w[i] for i in range(len(w) - 1))


def has_adj_zero(w: Word) -> bool:
    return any(w[i] == 0 and w[i + 1] == 0 for i in range(len(w) - 1))


def is_pword(w: Word) -> bool:
    return w.count(0) == 1


def main() -> None:
    max_n = 8
    words = enumerate_x(max_n)
    I: dict[int, set[Word]] = {}
    Y: dict[int, set[Word]] = {}
    Z: dict[int, set[Word]] = {}
    P: dict[int, set[Word]] = {}
    Right: dict[int, set[Word]] = {}
    Left: dict[int, set[Word]] = {}
    for n in range(1, max_n + 1):
        I[n] = {w for w in words[n] if not parses(w, words)[1]}
        Y[n] = set()
        # Y: right combs from [0]
        # enumerate via rebuild: start [0], close under ++ R(x) for x Xia
        P[n] = {w for w in words[n] if is_pword(w)}
        Right[n] = {w for w in P[n] if w[0] == 0}
        Left[n] = {w for w in P[n] if w[-1] == 0}

    # YWords
    Y[1] = {(0,)}
    for n in range(2, max_n + 1):
        s: set[Word] = set()
        for i in range(1, n):
            for u in Y[i]:
                for v in words[n - i]:
                    s.add(u + R(v))
        Y[n] = s

    Z[1] = {(0,)}
    for n in range(2, max_n + 1):
        s = set()
        for i in range(1, n):
            for u in words[i]:
                for v in Z[n - i]:
                    s.add(L(u) + v)
        Z[n] = s

    print("=== cardinalities vs A081696 / H ===")
    for n in range(1, max_n + 1):
        print(
            f"n={n} |X|={len(words[n])} |I|={len(I[n])} A081696(n-1)={a081696(n-1)} "
            f"|Y|={len(Y[n])} H(n-1)={H(n-1)} |Z\\I|={len(Z[n]-I[n])} "
            f"Wilf(n-1)={len(irreducible_pairs(n - 1)) if n >= 1 else 0}"
        )

    print("\n=== L(Left)++I and L(Right)++I ===")
    for n in range(2, max_n + 1):
        for kind, family in (("L", Left), ("R", Right), ("P", P)):
            good = bad = 0
            img_i = set()
            for k in range(1, n):
                for u in family[k]:
                    for v in I[n - k]:
                        w = L(u) + v
                        if w in I[n]:
                            good += 1
                            img_i.add(w)
                        else:
                            bad += 1
            print(
                f" n={n} {kind}: good={good} bad={bad} unique-in-I={len(img_i)} |I|={len(I[n])}"
            )

    print("\n=== I-words whose shortest left factor is Left / Right / middle ===")
    for n in range(2, max_n + 1):
        c = Counter()
        for w in I[n]:
            u, v = shortest_left(w, words)
            kind = (
                "L"
                if u in Left[len(u)]
                else "R"
                if u in Right[len(u)]
                else "M"
                if u in P[len(u)]
                else "?"
            )
            c[kind] += 1
        print(f" n={n} {dict(c)} |I|={len(I[n])}")

    print("\n=== adjacent zeros in X / I / Y ===")
    for n in range(1, max_n + 1):
        print(
            f" n={n} X={sum(has_adj_zero(w) for w in words[n])} "
            f"I={sum(has_adj_zero(w) for w in I[n])} "
            f"Y={sum(has_adj_zero(w) for w in Y[n])}"
        )

    print("\n=== I start letter / zero count / first return to 0 after start ===")
    for n in range(1, max_n + 1):
        starts = Counter(w[0] for w in I[n])
        zc = Counter(w.count(0) for w in I[n])
        print(f" n={n} start={dict(starts)} zeros={dict(zc)}")

    print("\n=== height-path: steps of I-words (n<=5 listed) ===")
    for n in range(1, 6):
        for w in sorted(I[n]):
            zp = zero_positions(w)
            print(
                f"  {w} steps={steps(w)} zeros={zp} "
                f"sl={None if n==1 else shortest_left(w, words)[0]}"
            )

    print("\n=== Y-words with no left parse vs rho(I) ===")
    for n in range(1, max_n + 1):
        jY = {w for w in Y[n] if not parses(w, words)[0]}
        rhoI = {rho(w) for w in I[n]}
        print(
            f" n={n} |Y∩J|={len(jY)} |rho(I)|={len(rhoI)} equal={jY==rhoI} "
            f"Y-with-neg={sum(any(x<0 for x in w) for w in Y[n])} "
            f"Y-with-left-parse={len(Y[n])-len(jY)}"
        )

    print("\n=== when is L(p)++v a right-parse (p PWord, v I)? remainder length ===")
    for n in range(2, max_n + 1):
        stats = Counter()
        examples = []
        for k in range(1, n):
            for p in P[k]:
                for v in I[n - k]:
                    w = L(p) + v
                    rp = parses(w, words)[1] if w in words[n] else None
                    if not w in words[n]:
                        stats["notX"] += 1
                        continue
                    if not rp:
                        stats["I"] += 1
                        continue
                    u, q = min(rp, key=lambda t: len(t[1]))
                    key = (
                        f"pL={p in Left[k]} pR={p in Right[k]} "
                        f"phead{p[0]} plast{p[-1]} |q|={len(q)} |v|={len(v)} "
                        f"qhead{q[0]} |u|={len(u)}"
                    )
                    stats[key] += 1
                    if len(examples) < 8:
                        examples.append((p, v, w, u, q))
        print(f" n={n} {stats.most_common(8)}")
        for ex in examples[:3]:
            print(f"    {ex}")

    print("\n=== first-return Callan counts vs I start/shortest ===")
    # Callan: 1 object size 1; 2 C_{k-1} objects size k>=2
    # Compare number of I-words with shortest left factor length k
    for n in range(2, max_n + 1):
        c = Counter()
        for w in I[n]:
            u, v = shortest_left(w, words)
            c[len(u)] += 1
        expected = {}
        for k in range(1, n):
            if k == 1:
                expected[k] = 1 * len(I[n - k])
            else:
                expected[k] = 2 * catalan(k - 1) * len(I[n - k])
        print(f" n={n} actual={dict(c)} naive-Q*I={expected}")

    print("\n=== I-words listed n<=6 with peel sequence of (kind,len,head,last,idx0) ===")
    for n in range(1, 7):
        for w in sorted(I[n]):
            cur = w
            peels = []
            while len(cur) >= 2:
                u, v = shortest_left(cur, words)
                kind = (
                    "L"
                    if u in Left[len(u)]
                    else "R"
                    if u in Right[len(u)]
                    else "M"
                )
                peels.append((kind, len(u), u[0], u[-1], u.index(0)))
                cur = v
            print(f"  {w} peels={peels}")

    print("\n=== rho(I) as Y: peel right P-factors ===")
    for n in range(1, 6):
        for w in sorted(I[n]):
            y = rho(w)
            cur = y
            peels = []
            while len(cur) >= 2:
                hit = shortest_right(cur, words)
                assert hit is not None
                u, p = hit
                peels.append((len(p), p[0], p[-1], p in Left[len(p)], p in Right[len(p)]))
                cur = u
            print(f"  I={w} Y={y} right-peels={peels}")

    print("\n=== Z\\I words n<=6 ===")
    for n in range(1, 7):
        extra = sorted(Z[n] - I[n])
        print(f" n={n} count={len(extra)}")
        for w in extra[:12]:
            print(
                f"  {w} Y={w in Y[n]} start={w[0]} last={w[-1]} "
                f"neg={any(x<0 for x in w)} sl={shortest_left(w, words)} "
                f"sr={shortest_right(w, words)}"
            )


if __name__ == "__main__":
    main()
