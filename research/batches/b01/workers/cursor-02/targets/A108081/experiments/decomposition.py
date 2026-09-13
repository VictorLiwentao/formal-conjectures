#!/usr/bin/env python3
"""Canonical decompositions for A108081 X-words.

Finite |X_n| checks through n=14 are already public. This script tests
candidate recurrences, cores, tails, and endpoint maps for a bijection.
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


def shortest_right(w: Word, by_len: dict[int, set[Word]]) -> tuple[Word, Word] | None:
    _, rp = parses(w, by_len)
    if not rp:
        return None
    m = min(len(v) for _, v in rp)
    hits = [(u, v) for u, v in rp if len(v) == m]
    assert len(hits) == 1
    return hits[0]


def longest_right(w: Word, by_len: dict[int, set[Word]]) -> tuple[Word, Word] | None:
    _, rp = parses(w, by_len)
    if not rp:
        return None
    m = max(len(v) for _, v in rp)
    hits = [(u, v) for u, v in rp if len(v) == m]
    assert len(hits) == 1
    return hits[0]


def shortest_left(w: Word, by_len: dict[int, set[Word]]) -> tuple[Word, Word] | None:
    lp, _ = parses(w, by_len)
    if not lp:
        return None
    m = min(len(u) for u, _ in lp)
    hits = [(u, v) for u, v in lp if len(u) == m]
    assert len(hits) == 1
    return hits[0]


def greedy_r_core(w: Word, by_len: dict[int, set[Word]]) -> tuple[Word, list[Word]]:
    """Peel shortest R-suffixes; return (core, peel sequence from the right)."""
    peels: list[Word] = []
    cur = w
    while True:
        hit = shortest_right(cur, by_len)
        if hit is None:
            return cur, peels
        pre, v = hit
        peels.append(v)
        cur = pre


def rebuild(core: Word, peels: list[Word]) -> Word:
    w = core
    for v in reversed(peels):
        w = w + R(v)
    return w


def a081696(n: int) -> int:
    # A081696(n) = Sum_k (k/(2n-k)) * C(2n-k, n-k) * F(k+1) for n>0, a(0)=1.
    if n == 0:
        return 1
    fib = [0, 1]
    for _ in range(n + 3):
        fib.append(fib[-1] + fib[-2])

    def F(m: int) -> int:
        return fib[m]

    s = 0
    for k in range(0, n + 1):
        if 2 * n - k == 0:
            continue
        s += k * comb(2 * n - k, n - k) * F(k + 1) // (2 * n - k)
    return s


def H(m: int) -> int:
    if m == 0:
        return 1
    return comb(2 * m - 1, m - 1)


def catalan(n: int) -> int:
    return comb(2 * n, n) // (n + 1)


def endpoint(w: Word) -> str:
    return {(0, 0): "A", (0, 1): "B", (-1, 0): "C", (-1, 1): "D"}[(w[0], w[-1])]


def main() -> None:
    max_n = 8
    words = enumerate_x(max_n)
    by_len = words

    print("=== endpoint class counts ===")
    for n in range(1, max_n + 1):
        c = Counter(endpoint(w) for w in words[n])
        print(
            f" n={n}: A={c['A']} B={c['B']} C={c['C']} D={c['D']} "
            f"|X|={len(words[n])} |X_{n-1}|={len(words[n-1]) if n > 1 else '-'}"
        )

    print("=== prepend-0 / append-0 maps ===")
    for n in range(1, max_n):
        start_neg = {w for w in words[n] if w[0] == -1}
        last_pos = {w for w in words[n] if w[-1] == 1}
        pre = {(0,) + w for w in start_neg}
        app = {w + (0,) for w in last_pos}
        in_x_pre = pre & words[n + 1]
        in_x_app = app & words[n + 1]
        first0 = {w for w in words[n + 1] if w[0] == 0}
        last0 = {w for w in words[n + 1] if w[-1] == 0}
        print(
            f" n={n}->{n+1}: prepend0 {len(in_x_pre)}/{len(start_neg)} in X, "
            f"image subset first0 {in_x_pre <= first0} covers first0 {in_x_pre == first0} "
            f"|first0|={len(first0)}; append0 {len(in_x_app)}/{len(last_pos)} in X, "
            f"covers last0 {in_x_app == last0}"
        )

    print("=== R-irreducible / L-irreducible counts vs A081696(n-1) ===")
    I = {}
    J = {}
    for n in range(1, max_n + 1):
        I[n] = {w for w in words[n] if not parses(w, by_len)[1]}
        J[n] = {w for w in words[n] if not parses(w, by_len)[0]}
        print(
            f" n={n}: I={len(I[n])} J={len(J[n])} A081696({n-1})={a081696(n-1)} "
            f"rho(I)=J { {rho(w) for w in I[n]} == J[n] }"
        )

    print("=== L-only last letters / R-only first letters ===")
    for n in range(1, max_n + 1):
        I_last = Counter(w[-1] for w in I[n])
        J_first = Counter(w[0] for w in J[n])
        print(f" n={n}: I lasts {sorted(I_last.items())} J firsts {sorted(J_first.items())}")

    print("=== greedy R-core length histogram ===")
    cores: dict[int, dict[Word, list[Word]]] = {n: defaultdict(list) for n in range(1, max_n + 1)}
    for n in range(1, max_n + 1):
        hist = Counter()
        rebuild_ok = 0
        for w in words[n]:
            c, peels = greedy_r_core(w, by_len)
            hist[len(c)] += 1
            cores[n][c].append(w)
            if rebuild(c, peels) == w:
                rebuild_ok += 1
        print(f" n={n}: core-len {sorted(hist.items())} rebuild {rebuild_ok}/{len(words[n])}")

    print("=== fiber sizes over R-cores (words with a given greedy core) ===")
    for n in range(1, max_n + 1):
        by_clen: dict[int, list[int]] = defaultdict(list)
        for c, ws in cores[n].items():
            by_clen[len(c)].append(len(ws))
        parts = []
        for k in sorted(by_clen):
            sizes = by_clen[k]
            parts.append(
                f"k={k}: #cores={len(sizes)} fiber-min={min(sizes)} max={max(sizes)} "
                f"uniq={len(set(sizes))} H_{n-k}={H(n-k)}"
            )
        print(f" n={n}: " + " | ".join(parts))

    print("=== convolution tests vs |X_n| ===")
    B = {n: len(words[n]) for n in range(1, max_n + 1)}
    In = {n: len(I[n]) for n in range(1, max_n + 1)}
    for n in range(1, max_n + 1):
        conv_IH = sum(In[k] * H(n - k) for k in range(1, n + 1))
        conv_IY = sum(In[k] * catalan(n - k) for k in range(1, n + 1))  # |Y_{n-k+1}| = C_{n-k}?
        # |Y_m| = Catalan(m-1) if Y is fully R-reducible to [0]
        conv_IYshift = sum(In[k] * catalan(n - k) for k in range(1, n + 1))
        Ycount = {}
        for m in range(1, n + 1):
            Ycount[m] = sum(1 for w in words[m] if greedy_r_core(w, by_len)[0] == (0,))
        conv_IY2 = sum(In[k] * Ycount.get(n - k + 1, 0) for k in range(1, n + 1))
        conv_IB = In[n] + sum(In[k] * B[n - k] for k in range(1, n))
        print(
            f" n={n}: |X|={B[n]} I*H={conv_IH} I*C={conv_IYshift} "
            f"I*Y_{{n-k+1}}={conv_IY2} I+I*B={conv_IB}"
        )

    print("=== fully R-reducible words Y_n (core=[0]) vs Catalan and H ===")
    for n in range(1, max_n + 1):
        Yn = [w for w in words[n] if greedy_r_core(w, by_len)[0] == (0,)]
        print(
            f" n={n}: |Y|={len(Yn)} C_{n-1}={catalan(n-1)} H_{n-1}={H(n-1)} "
            f"H_n={H(n)}"
        )

    print("=== shortest R-peel: is remainder R-irreducible? is peel R-irreducible? ===")
    for n in range(2, max_n + 1):
        has_r = 0
        rem_I = 0
        peel_I = 0
        rem_any = 0
        for w in words[n]:
            hit = shortest_right(w, by_len)
            if hit is None:
                continue
            has_r += 1
            pre, v = hit
            rem_any += 1
            if pre in I[len(pre)]:
                rem_I += 1
            if v in I[len(v)]:
                peel_I += 1
        print(
            f" n={n}: hasR={has_r} shortest-rem-in-I={rem_I} shortest-peel-in-I={peel_I}"
        )

    print("=== longest R-peel: is remainder R-irreducible? is peel R-irreducible? ===")
    for n in range(2, max_n + 1):
        has_r = 0
        rem_I = 0
        peel_I = 0
        for w in words[n]:
            hit = longest_right(w, by_len)
            if hit is None:
                continue
            has_r += 1
            pre, v = hit
            if pre in I[len(pre)]:
                rem_I += 1
            if v in I[len(v)]:
                peel_I += 1
        print(
            f" n={n}: hasR={has_r} longest-rem-in-I={rem_I} longest-peel-in-I={peel_I}"
        )

    print("=== shortest L-peel: is left factor L-irreducible? ===")
    for n in range(2, max_n + 1):
        has_l = 0
        left_J = 0
        right_any = 0
        for w in words[n]:
            hit = shortest_left(w, by_len)
            if hit is None:
                continue
            has_l += 1
            u, v = hit
            if u in J[len(u)]:
                left_J += 1
            if v in words[len(v)]:
                right_any += 1
        print(f" n={n}: hasL={has_l} shortest-u-in-J={left_J}")

    print("=== words of length 3 with parses ===")
    for w in sorted(words[3]):
        lp, rp = parses(w, by_len)
        c, peels = greedy_r_core(w, by_len)
        print(f"  {w} ep={endpoint(w)} L={lp} R={rp} core={c} peels={peels}")

    print("=== words of length 4 with greedy R-core ===")
    for w in sorted(words[4]):
        c, peels = greedy_r_core(w, by_len)
        lp, rp = parses(w, by_len)
        print(
            f"  {w} ep={endpoint(w)} core={c} peels={peels} "
            f"#L={len(lp)} #R={len(rp)}"
        )

    print("=== Kotesovec recurrence on |X_n| = a(n-1) ===")
    # n*(n+1)*a(n) = 2*(4n^2+3n-6)a(n-1) - (15n^2+7n-48)a(n-2) - 2(n+2)(2n-3)a(n-3)
    seq = [len(words[n]) for n in range(1, max_n + 1)]  # a(0), a(1), ...
    print(" seq", seq)
    for n in range(3, max_n):
        lhs = n * (n + 1) * seq[n]
        rhs = (
            2 * (4 * n * n + 3 * n - 6) * seq[n - 1]
            - (15 * n * n + 7 * n - 48) * seq[n - 2]
            - 2 * (n + 2) * (2 * n - 3) * seq[n - 3]
        )
        print(f" a({n}) rec: lhs={lhs} rhs={rhs} ok={lhs == rhs}")

    print("=== first-return of zeros / positions of 0 ===")
    for n in range(1, min(6, max_n) + 1):
        print(f" n={n}")
        for w in sorted(words[n]):
            zs = [i for i, x in enumerate(w) if x == 0]
            print(f"  {w} zeros@{zs} ep={endpoint(w)}")

    print("=== can every R-word be written as J-irreducible-left ++ r(any)? unique? ===")
    # L-irreducible left + r(v)
    for n in range(2, max_n + 1):
        hits = 0
        uniq = 0
        for w in words[n]:
            _, rp = parses(w, by_len)
            good = [(u, v) for u, v in rp if u in J[len(u)]]
            if good:
                hits += 1
            if len(good) == 1:
                uniq += 1
        print(
            f" n={n}: has J-left R-parse {hits}/{len(words[n])-len(I[n])} expected-hasR "
            f"unique {uniq}"
        )

    print("=== I_n last=0 always? words in I listed for n<=4 ===")
    for n in range(1, 5):
        for w in sorted(I[n]):
            print(f"  I_{n} {w}")

    print("=== try: X_n classified by last letter and unique longest R ===")
    for n in range(1, max_n + 1):
        lastc = Counter(w[-1] for w in words[n])
        print(f" n={n}: last {sorted(lastc.items())}")

    print("=== generate tails from core [0] vs other cores of same length ===")
    # For each n, group tails w[k:] for greedy core length k
    for n in range(2, min(6, max_n) + 1):
        tails_by_k: dict[int, dict[Word, set[Word]]] = defaultdict(lambda: defaultdict(set))
        for w in words[n]:
            c, _ = greedy_r_core(w, by_len)
            tails_by_k[len(c)][c].add(w[len(c) :])
        for k in sorted(tails_by_k):
            core_tails = tails_by_k[k]
            sizes = {core: len(ts) for core, ts in core_tails.items()}
            union = set().union(*core_tails.values()) if core_tails else set()
            common = set.intersection(*core_tails.values()) if core_tails else set()
            print(
                f" n={n} k={k}: #cores={len(core_tails)} tail-card {Counter(sizes.values())} "
                f"|union tails|={len(union)} |common|={len(common)} H_{n-k}={H(n-k)}"
            )


if __name__ == "__main__":
    main()
