#!/usr/bin/env python3
"""Where do two-zero Xia words split, in the PWord ++ r(v with -1) case?"""
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


def concat_splits(w: Word, by_len) -> list[int]:
    n = len(w)
    return [m for m in range(1, n) if w[:m] in by_len[m] and w[m:] in by_len[n - m]]


def main() -> None:
    max_n = 7
    words = enumerate_x(max_n)
    P = {n: {w for w in words[n] if w.count(0) == 1} for n in range(1, max_n + 1)}

    print("=== constructors that produce multi-zero words ===")
    for n in range(2, max_n + 1):
        stats = {
            "left_v_multi": 0,
            "left_v_P_u_has1": 0,
            "right_u_multi": 0,
            "right_u_P_v_has_neg1": 0,
            "both_ctors": 0,
        }
        examples = []
        for w in words[n]:
            if w.count(0) < 2:
                continue
            lefts = []
            rights = []
            for i in range(1, n):
                pre, suf = w[:i], w[i:]
                u = tuple(x + 1 for x in reversed(pre))  # R^{-1} wait that's not L
                # left parse: w = L(u) ++ v  => u = R(pre), v = suf
                uu = R(pre)
                if uu in words[i] and suf in words[n - i]:
                    lefts.append((uu, suf))
                vv = L(suf)
                if pre in words[i] and vv in words[n - i]:
                    rights.append((pre, vv))
            if lefts and rights:
                stats["both_ctors"] += 1
            for uu, suf in lefts:
                if suf.count(0) >= 2:
                    stats["left_v_multi"] += 1
                elif suf.count(0) == 1 and uu.count(1) >= 1:
                    stats["left_v_P_u_has1"] += 1
            for pre, vv in rights:
                if pre.count(0) >= 2:
                    stats["right_u_multi"] += 1
                elif pre.count(0) == 1 and vv.count(-1) >= 1:
                    stats["right_u_P_v_has_neg1"] += 1
                    if n <= 5 and len(examples) < 8:
                        splits = concat_splits(w, words)
                        examples.append((w, pre, vv, splits, [(s, w[s:]) for s in splits]))
        print(f" n={n}: {stats}")
        for ex in examples:
            print("   ", ex)

    print("=== hard right subcase: PWord u, v has -1; split vs |u| and idx of -1 ===")
    for n in range(3, max_n + 1):
        rel = []
        fail = 0
        for i in range(1, n):
            for u in P[i]:
                for v in words[n - i]:
                    if v.count(-1) < 1:
                        continue
                    w = u + R(v)
                    if w not in words[n] or w.count(0) < 2:
                        continue
                    splits = concat_splits(w, words)
                    if not splits:
                        fail += 1
                        continue
                    # relative positions
                    for m in splits:
                        rel.append(
                            (
                                m - i,
                                v.index(-1) if -1 in v else None,
                                len(v) - 1 - (n - m) if n - m <= len(v) else None,
                                m > i,
                            )
                        )
        from collections import Counter

        # m - |u|: how far into r(v)
        c = Counter(x[0] for x in rel)
        pos = Counter(x[3] for x in rel)
        print(f" n={n}: fail={fail} m-|u| hist={dict(sorted(c.items()))} m>|u|={pos}")

    print("=== try split at |u| + (position of last 0 in r(v) from start of suffix) ===")
    for n in range(3, max_n + 1):
        pred_ok = 0
        pred_fail = 0
        for i in range(1, n):
            for u in P[i]:
                for v in words[n - i]:
                    if v.count(-1) < 1:
                        continue
                    w = u + R(v)
                    if w not in words[n] or w.count(0) < 2:
                        continue
                    rv = R(v)
                    # last 0 in r(v) — since -1 in v, 0 in r(v)
                    zeros = [j for j, x in enumerate(rv) if x == 0]
                    if not zeros:
                        pred_fail += 1
                        continue
                    # try each 0 in r(v) as start of drop
                    hit = False
                    for j in zeros:
                        m = i + j
                        if m <= 0 or m >= n:
                            continue
                        if w[:m] in words[m] and w[m:] in words[n - m]:
                            hit = True
                            break
                    if hit:
                        pred_ok += 1
                    else:
                        pred_fail += 1
                        if pred_fail <= 3:
                            print(" fail", w, u, v, concat_splits(w, words), rv)
        print(f" n={n}: split_at_0_in_r(v) ok={pred_ok} fail={pred_fail}")

    print("=== try: first -1 in v, drop = R(v[:idx+1]) ===")
    for n in range(3, max_n + 1):
        ok = 0
        fail = 0
        fails = []
        for i in range(1, n):
            for u in P[i]:
                for v in words[n - i]:
                    if -1 not in v:
                        continue
                    w = u + R(v)
                    if w not in words[n] or w.count(0) < 2:
                        continue
                    idx = v.index(-1)
                    take_v = v[: idx + 1]
                    drop = R(take_v)
                    left = u + R(v[idx + 1 :]) if idx + 1 < len(v) else u
                    # proposed split: w = left ++ drop ? 
                    # w = u ++ R(v) = u ++ R(v[idx+1:] ++ v[:idx+1]) wait no
                    # R(a++b)=R(b)++R(a)
                    # v = v[:idx+1] ++ v[idx+1:]
                    # R(v) = R(v[idx+1:]) ++ R(v[:idx+1])
                    # w = u ++ R(v[idx+1:]) ++ R(v[:idx+1]) = left ++ drop
                    recon = left + drop
                    m = len(left)
                    good = (
                        recon == w
                        and 0 < m < n
                        and left in words.get(len(left), set())
                        and drop in words.get(len(drop), set())
                    )
                    if good:
                        ok += 1
                    else:
                        fail += 1
                        if len(fails) < 3:
                            fails.append(
                                (
                                    w,
                                    u,
                                    v,
                                    idx,
                                    left,
                                    drop,
                                    recon == w,
                                    left in words.get(len(left), set()),
                                    drop in words.get(len(drop), set()),
                                )
                            )
        print(f" n={n}: first_-1 ok={ok} fail={fail} e.g.={fails[:1]}")

    print("=== last -1 in v ===")
    for n in range(3, max_n + 1):
        ok = 0
        fail = 0
        fails = []
        for i in range(1, n):
            for u in P[i]:
                for v in words[n - i]:
                    if -1 not in v:
                        continue
                    w = u + R(v)
                    if w not in words[n] or w.count(0) < 2:
                        continue
                    idx = len(v) - 1 - v[::-1].index(-1)
                    left = u + R(v[idx + 1 :]) if idx + 1 < len(v) else u
                    drop = R(v[: idx + 1])
                    recon = left + drop
                    m = len(left)
                    good = (
                        recon == w
                        and 0 < m < n
                        and left in words.get(len(left), set())
                        and drop in words.get(len(drop), set())
                    )
                    if good:
                        ok += 1
                    else:
                        fail += 1
                        if len(fails) < 2:
                            fails.append((w, u, v, idx, left, drop))
        print(f" n={n}: last_-1 ok={ok} fail={fail} e.g.={fails[:1]}")


if __name__ == "__main__":
    main()
