#!/usr/bin/env python3
"""Search for exact structural bijections for A108081.

Finite counts are not a proof. This looks for maps and invariants that
could become a bijection in Lean.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from math import comb

Word = tuple[int, ...]


def L(w: Word) -> Word:
    return tuple(x - 1 for x in reversed(w))


def R(w: Word) -> Word:
    return tuple(x + 1 for x in reversed(w))


def rho(w: Word) -> Word:
    return tuple(-x for x in reversed(w))


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
                    nxt.add(u + R(v))
        words[n] = nxt
    return words


def parses(w: Word, by_len: dict[int, set[Word]]):
    left = []
    right = []
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


def shortest_right(w, by_len):
    _, rp = parses(w, by_len)
    if not rp:
        return None
    m = min(len(v) for _, v in rp)
    hits = [(u, v) for u, v in rp if len(v) == m]
    assert len(hits) == 1
    return hits[0]


def greedy_r_core(w, by_len):
    peels = []
    cur = w
    while True:
        hit = shortest_right(cur, by_len)
        if hit is None:
            return cur, peels
        pre, v = hit
        peels.append(v)
        cur = pre


def H(m: int) -> int:
    if m == 0:
        return 1
    return comb(2 * m - 1, m - 1)


def endpoint(w: Word) -> str:
    return {(0, 0): "A", (0, 1): "B", (-1, 0): "C", (-1, 1): "D"}[(w[0], w[-1])]


def a_val(n: int) -> int:
    # a(n) = sum_k C(n+k-1, k) * F(n-k+1)
    fib = [0, 1]
    for _ in range(n + 4):
        fib.append(fib[-1] + fib[-2])
    s = 0
    for k in range(n + 1):
        s += comb(n + k - 1, k) * fib[n - k + 1]
    return s


def main() -> None:
    max_n = 8
    words = enumerate_x(max_n)
    by_len = words

    I = {
        n: {w for w in words[n] if not parses(w, by_len)[1]}
        for n in range(1, max_n + 1)
    }
    Y = {
        n: {w for w in words[n] if greedy_r_core(w, by_len)[0] == (0,)}
        for n in range(1, max_n + 1)
    }
    B = {n: {w for w in words[n] if endpoint(w) == "B"} for n in range(1, max_n + 1)}
    A = {n: {w for w in words[n] if endpoint(w) == "A"} for n in range(1, max_n + 1)}
    C = {n: {w for w in words[n] if endpoint(w) == "C"} for n in range(1, max_n + 1)}
    D = {n: {w for w in words[n] if endpoint(w) == "D"} for n in range(1, max_n + 1)}

    print("=== max/min entries of I, J, Y ===")
    for n in range(1, max_n + 1):
        Imax = max((max(w) for w in I[n]), default=None)
        Imin = min((min(w) for w in I[n]), default=None)
        Ymax = max((max(w) for w in Y[n]), default=None)
        Ymin = min((min(w) for w in Y[n]), default=None)
        pos_in_I = sum(1 for w in I[n] if max(w) > 0)
        neg_in_Y = sum(1 for w in Y[n] if min(w) < 0)
        print(
            f" n={n}: I min={Imin} max={Imax} #with_pos={pos_in_I}/{len(I[n])} "
            f"Y min={Ymin} max={Ymax} #with_neg={neg_in_Y}/{len(Y[n])}"
        )

    print("=== all entries of I-words n<=5 ===")
    for n in range(1, 6):
        for w in sorted(I[n]):
            print(f"  I_{n} {w} max={max(w)}")

    print("=== Y-words n<=4 ===")
    for n in range(1, 5):
        for w in sorted(Y[n]):
            print(f"  Y_{n} {w} peels={greedy_r_core(w, by_len)[1]}")

    print("=== rebuild I x Y: split-inside-core? fibre injective? ===")
    for n in range(1, max_n + 1):
        seen = {}
        clash = 0
        split_inside = 0
        peel_mismatch = 0
        not_I_core = 0
        for k in range(1, n + 1):
            m = n - k + 1
            if m not in Y:
                continue
            for c in I[k]:
                for y in Y[m]:
                    w = c + y[1:]
                    if w in seen:
                        clash += 1
                    seen[w] = (c, y)
                    if w not in words[n]:
                        print("NOT IN X", w, c, y)
                    core, peels = greedy_r_core(w, by_len)
                    if core != c:
                        not_I_core += 1
                    yp = greedy_r_core(y, by_len)[1]
                    if peels != yp:
                        peel_mismatch += 1
                    hit = shortest_right(w, by_len)
                    if hit is not None and len(hit[0]) < len(c):
                        split_inside += 1
        print(
            f" n={n}: |image|={len(seen)} |X|={len(words[n])} clash={clash} "
            f"split_inside={split_inside} peel_mismatch={peel_mismatch} "
            f"wrong_core={not_I_core}"
        )

    print("=== |B_n| vs |X_{n-1}| and class recurrences ===")
    for n in range(1, max_n + 1):
        print(
            f" n={n}: A={len(A[n])} B={len(B[n])} C={len(C[n])} D={len(D[n])} "
            f"|X_{n-1}|={len(words[n - 1]) if n > 1 else '-'} "
            f"2B+A+D={2 * len(B[n]) + len(A[n]) + len(D[n])}"
        )

    print("=== maps X_{n-1} -> B_n candidates ===")

    def try_map(name, fn, src, dst):
        img = {}
        fail = 0
        for w in src:
            try:
                out = fn(w)
            except Exception:
                fail += 1
                continue
            if out not in dst:
                fail += 1
                continue
            img.setdefault(out, []).append(w)
        multi = sum(1 for vs in img.values() if len(vs) != 1)
        print(
            f"  {name}: image {len(img)}/{len(dst)} src {len(src)} "
            f"fail {fail} nonunique {multi} bijective "
            f"{len(img) == len(dst) == len(src) and multi == 0 and fail == 0}"
        )

    for n in range(2, max_n + 1):
        print(f" -- n={n} --")
        src = words[n - 1]
        dst = B[n]
        try_map("w++[1] if first0 else [0]++R(w)",
                lambda w: w + (1,) if w[0] == 0 else (0,) + R(w), src, dst)
        try_map("[0]++R(w) if last0 else w++[1]",
                lambda w: (0,) + R(w) if w[-1] == 0 else w + (1,), src, dst)
        try_map("[0]++R(w) always", lambda w: (0,) + R(w), src, dst)
        try_map("w++[1] always", lambda w: w + (1,), src, dst)
        try_map("R(w)++[0] wait no", lambda w: (0,) + w, src, dst)
        try_map("0::w if first-1 else w++[1]",
                lambda w: (0,) + w if w[0] == -1 else w + (1,), src, dst)
        try_map("l(w)++[1]", lambda w: L(w) + (1,), src, dst)
        try_map("rho then [0]++R", lambda w: (0,) + R(rho(w)), src, dst)

        # parse-based: take w ++ [1] (always X), then drop something
        def via_append_one(w):
            z = w + (1,)
            hit = shortest_right(z, by_len)
            if hit is None:
                return None
            u, v = hit
            return u + v[1:] if v else u

        # shortest peel of words in B
        print("  inverse search: B -> length n-1 X via simple slices")
        for w in list(dst)[:0]:
            pass
        cands = []
        # For every B word, list X_{n-1} words obtained by deleting one index
        recovered = []
        for w in dst:
            opts = []
            for i in range(n):
                ww = w[:i] + w[i + 1 :]
                if ww in src:
                    opts.append(("del", i, ww))
            if w[0] == 0:
                v = L(w[1:])
                if v in src:
                    opts.append(("Ltail", v))
            if w[-1] == 1 and w[:-1] in src:
                opts.append(("droplast", w[:-1]))
            recovered.append((w, opts))
        # count how many have unique recovery of a given type
        kinds = Counter()
        for w, opts in recovered:
            kinds[tuple(o[0] for o in opts)] += 1
        print(f"  B recovery kind histogram (first 12): {kinds.most_common(12)}")

    print("=== statistic i for |slice| = C(2m-i, m+i) on X_{m+1} ===")
    for m in range(0, max_n):
        xs = words[m + 1]
        target = []
        i = 0
        while True:
            val = comb(2 * m - i, m + i) if m + i <= 2 * m - i else 0
            if i > m:
                break
            target.append(val)
            i += 1
        # try stats
        stats = {
            "nzeros": lambda w: w.count(0) - 1,
            "max": lambda w: max(w),
            "min": lambda w: -min(w),
            "sum": lambda w: sum(x for x in w if x > 0),
            "npeels": lambda w: len(greedy_r_core(w, by_len)[1]),
            "corelen": lambda w: len(greedy_r_core(w, by_len)[0]) - 1,
            "npos": lambda w: sum(1 for x in w if x > 0),
            "nneg": lambda w: sum(1 for x in w if x < 0),
            "sumabs": lambda w: sum(abs(x) for x in w),
            "first0last1": lambda w: (w[0] == 0) + (w[-1] == 1),
        }
        print(f" m={m} |X|={len(xs)} target_slices={target} sum={sum(target)}")
        for name, fn in stats.items():
            hist = Counter(fn(w) for w in xs)
            vals = [hist.get(i, 0) for i in range(len(target))]
            extra = {k: v for k, v in hist.items() if k < 0 or k >= len(target)}
            if vals == target and not extra:
                print(f"   MATCH {name}")
            # also try sorted hist vs target ignore keys
            if sorted(hist.values(), reverse=True) == sorted(t for t in target if t):
                print(f"   same-multiset {name} {dict(sorted(hist.items()))}")

    print("=== first peel of Y-words: which family? ===")
    for n in range(2, max_n + 1):
        kinds = Counter()
        heads = Counter()
        Ipeel = 0
        Ypeel = 0
        for y in Y[n]:
            hit = shortest_right(y, by_len)
            assert hit is not None
            u, v = hit
            kinds[endpoint(v)] += 1
            heads[v[0]] += 1
            if v in I[len(v)]:
                Ipeel += 1
            if v in Y[len(v)]:
                Ypeel += 1
            if u not in Y[len(u)]:
                print(" u not Y", y, u, v)
        print(
            f" n={n}: peel-ep {sorted(kinds.items())} peel-head {sorted(heads.items())} "
            f"peel-in-I {Ipeel}/{len(Y[n])} peel-in-Y {Ypeel}/{len(Y[n])}"
        )

    print("=== A_n, D_n vs previous classes ===")
    for n in range(2, max_n + 1):
        # prepend 0 on C_n? C is first -1 last 0
        preC = {(0,) + w for w in C[n - 1]}
        print(
            f" n={n}: 0++C_{n-1} in X {len(preC & words[n])}/{len(C[n-1])} "
            f"subset A {preC <= A[n]} |A|={len(A[n])} "
            f"++[0] on B {len({w + (0,) for w in B[n - 1]} & words[n])}/{len(B[n - 1])}"
        )

    print("=== Manyama k = n-fib index: zeros besides first/last? ===")
    for n in range(1, min(6, max_n) + 1):
        print(f" n={n} Y words with running min")
        for w in sorted(Y[n]):
            print(f"  {w}")


if __name__ == "__main__":
    main()
