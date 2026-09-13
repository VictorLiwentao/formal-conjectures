#!/usr/bin/env python3
"""Structure experiments for A108081 X-words.

Counts through length 14 are already public. This script looks for a canonical
parse or statistic that could support a bijection with a(n-1).
"""
from __future__ import annotations

from collections import Counter, defaultdict
from math import comb
from typing import Iterable

Word = tuple[int, ...]

def fib(n: int) -> int:
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a

def nat_sub(x: int, y: int) -> int:
    return x - y if x >= y else 0

def nat_choose(n: int, k: int) -> int:
    if k < 0 or n < 0 or k > n:
        return 0
    return comb(n, k)

def a_barry(n: int) -> int:
    # Match Lean Nat subtraction: (n+k-1).choose k.
    return sum(nat_choose(nat_sub(n + k, 1), k) * fib(n - k + 1) for k in range(n + 1))

def a_main(n: int) -> int:
    return sum(comb(2 * n - i, n + i) for i in range(n + 1))

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

def parses(w: Word, by_len: dict[int, set[Word]]) -> tuple[list[tuple[Word, Word]], list[tuple[Word, Word]]]:
    left: list[tuple[Word, Word]] = []
    right: list[tuple[Word, Word]] = []
    n = len(w)
    for i in range(1, n):
        pre, suf = w[:i], w[i:]
        u = R(pre)  # inverse of L
        if u in by_len[i] and suf in by_len[n - i]:
            left.append((u, suf))
        v = L(suf)  # inverse of R
        if pre in by_len[i] and v in by_len[n - i]:
            right.append((pre, v))
    return left, right

def triples(w: Word, by_len: dict[int, set[Word]]) -> list[tuple[Word, Word, Word]]:
    n = len(w)
    out: list[tuple[Word, Word, Word]] = []
    for i in range(1, n - 1):
        for k in range(1, n - i):
            pre, mid, suf = w[:i], w[i:i + k], w[i + k:]
            u = R(pre)
            v = L(suf)
            if u in by_len[i] and mid in by_len[k] and v in by_len[n - i - k]:
                out.append((u, mid, v))
    return out

def greedy_peel_shortest_right(w: Word, by_len: dict[int, set[Word]]) -> Word | None:
    """Peel shortest R-suffix if any, else shortest L-prefix. Return core or None."""
    cur = w
    seen: set[Word] = set()
    while cur != (0,):
        if cur in seen:
            return None
        seen.add(cur)
        n = len(cur)
        peeled = False
        for j in range(1, n):
            suf = cur[n - j :]
            pre = cur[: n - j]
            v = L(suf)
            if pre and v in by_len[j] and pre in by_len[n - j]:
                cur = pre
                peeled = True
                break
        if peeled:
            continue
        for i in range(1, n):
            pre = cur[:i]
            suf = cur[i:]
            u = R(pre)
            if suf and u in by_len[i] and suf in by_len[n - i]:
                cur = suf
                peeled = True
                break
        if not peeled:
            return None
    return cur

def main() -> None:
    max_n = 8
    print("=== formula agreement n=0..20 ===")
    bad = [n for n in range(21) if a_barry(n) != a_main(n)]
    print("mismatches", bad if bad else "NONE")

    words = enumerate_x(max_n)
    print("=== |X_n| vs a(n-1) ===")
    for n in range(1, max_n + 1):
        got = len(words[n])
        exp = a_main(n - 1)
        print(f" n={n}: |X|={got} a({n-1})={exp} match={got == exp}")

    print("=== L/R inverse and anti-homomorphism spot checks ===")
    sample = list(words[4])[:20]
    for w in sample:
        assert L(R(w)) == w and R(L(w)) == w
    u, v = (0, 1), (-1, 0)
    assert L(u + v) == L(v) + L(u)
    assert R(u + v) == R(v) + R(u)
    print(" ok")

    print("=== constructor injectivity and parse multiplicity ===")
    for n in range(2, max_n + 1):
        left_map: dict[Word, list[tuple[Word, Word]]] = defaultdict(list)
        right_map: dict[Word, list[tuple[Word, Word]]] = defaultdict(list)
        for i in range(1, n):
            j = n - i
            for u in words[i]:
                for v in words[j]:
                    left_map[L(u) + v].append((u, v))
                    right_map[u + R(v)].append((u, v))
        left_coll = sum(1 for ps in left_map.values() if len(ps) > 1)
        right_coll = sum(1 for ps in right_map.values() if len(ps) > 1)
        left_only = sum(1 for w in words[n] if w in left_map and w not in right_map)
        right_only = sum(1 for w in words[n] if w in right_map and w not in left_map)
        both = sum(1 for w in words[n] if w in left_map and w in right_map)
        neither = sum(1 for w in words[n] if w not in left_map and w not in right_map)
        c = sum(len(words[i]) * len(words[n - i]) for i in range(1, n))
        print(
            f" n={n}: L-images={len(left_map)} R-images={len(right_map)} "
            f"L-coll-words={left_coll} R-coll-words={right_coll} "
            f"derivL={c} derivR={c} Lonly={left_only} Ronly={right_only} both={both} neither={neither}"
        )

    print("=== parse multiplicity histogram ===")
    for n in range(2, max_n + 1):
        hist = Counter()
        for w in words[n]:
            lp, rp = parses(w, words)
            hist[(len(lp), len(rp))] += 1
        print(f" n={n}: {sorted(hist.items())}")

    print("=== unique shortest L-prefix / R-suffix among X-words ===")
    for n in range(2, max_n + 1):
        uniq_short_L = uniq_short_R = 0
        for w in words[n]:
            lp, rp = parses(w, words)
            if lp:
                m = min(len(u) for u, _ in lp)
                uniq_short_L += int(sum(1 for u, _ in lp if len(u) == m) == 1)
            else:
                uniq_short_L += 1
            if rp:
                m = min(len(v) for _, v in rp)
                uniq_short_R += int(sum(1 for _, v in rp if len(v) == m) == 1)
            else:
                uniq_short_R += 1
        print(f" n={n}: unique shortest L {uniq_short_L}/{len(words[n])} unique shortest R {uniq_short_R}/{len(words[n])}")

    print("=== greedy shortest-R then shortest-L reduces to [0] ===")
    for n in range(1, max_n + 1):
        ok = sum(1 for w in words[n] if greedy_peel_shortest_right(w, words) == (0,))
        print(f" n={n}: {ok}/{len(words[n])}")

    print("=== L(u)++z++R(v) triple representations for overlap words ===")
    for n in range(2, max_n + 1):
        hist = Counter()
        overlap = 0
        uniq_triple = 0
        for w in words[n]:
            lp, rp = parses(w, words)
            if lp and rp:
                overlap += 1
                ts = triples(w, words)
                hist[len(ts)] += 1
                if len(ts) == 1:
                    uniq_triple += 1
        print(f" n={n}: overlap={overlap} triple-hist={sorted(hist.items())} unique-triple={uniq_triple}")

    print("=== first/last/min/max/sum statistics ===")
    for n in range(1, min(6, max_n) + 1):
        print(f" n={n}")
        for w in sorted(words[n]):
            lp, rp = parses(w, words)
            print(
                f"  {w} first={w[0]} last={w[-1]} min={min(w)} max={max(w)} "
                f"sum={sum(w)} L={len(lp)} R={len(rp)}"
            )

    print("=== first-letter distribution ===")
    for n in range(1, max_n + 1):
        c = Counter(w[0] for w in words[n])
        print(f" n={n}: {sorted(c.items())}")

    print("=== last-letter distribution ===")
    for n in range(1, max_n + 1):
        c = Counter(w[-1] for w in words[n])
        print(f" n={n}: {sorted(c.items())}")

    print("=== whether first<=0 and last>=0 ===")
    for n in range(1, max_n + 1):
        bad_first = sum(1 for w in words[n] if w[0] > 0)
        bad_last = sum(1 for w in words[n] if w[-1] < 0)
        print(f" n={n}: first>0 {bad_first} last<0 {bad_last}")

    print("=== right-only words: those with no L-parse ===")
    for n in range(1, min(5, max_n) + 1):
        for w in sorted(words[n]):
            lp, rp = parses(w, words)
            if not lp:
                print(f" n={n} R-only {w} Rparses={rp}")

    print("=== left-only words: those with no R-parse ===")
    for n in range(1, min(5, max_n) + 1):
        for w in sorted(words[n]):
            lp, rp = parses(w, words)
            if not rp:
                print(f" n={n} L-only {w} Lparses={lp}")

    print("=== test: every word contains 0? ===")
    for n in range(1, max_n + 1):
        missing = sum(1 for w in words[n] if 0 not in w)
        print(f" n={n}: missing0={missing}")

    print("=== test: unique longest L-prefix ===")
    for n in range(2, max_n + 1):
        uniq = 0
        for w in words[n]:
            lp, _ = parses(w, words)
            if not lp:
                uniq += 1
                continue
            m = max(len(u) for u, _ in lp)
            uniq += int(sum(1 for u, _ in lp if len(u) == m) == 1)
        print(f" n={n}: {uniq}/{len(words[n])}")

    print("=== test: peel maximal R-suffix then remainder in X ===")
    # remainder after removing longest R-suffix
    for n in range(2, max_n + 1):
        ok = 0
        for w in words[n]:
            _, rp = parses(w, words)
            if not rp:
                ok += 1
                continue
            m = max(len(v) for _, v in rp)
            longest = [(u, v) for u, v in rp if len(v) == m]
            if len(longest) == 1 and longest[0][0] in words[n - m]:
                ok += 1
        print(f" n={n}: unique longest R-suffix {ok}/{len(words[n])}")

    print("=== range of entries ===")
    for n in range(1, max_n + 1):
        lo = min(min(w) for w in words[n])
        hi = max(max(w) for w in words[n])
        print(f" n={n}: [{lo},{hi}] vs [1-n,n-1]=[{1-n},{n-1}]")

if __name__ == "__main__":
    main()
