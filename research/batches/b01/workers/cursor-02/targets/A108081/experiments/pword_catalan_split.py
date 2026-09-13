#!/usr/bin/env python3
"""Catalan decomposition candidates for one-zero Xia words (P-words)."""
from math import comb

Word = tuple[int, ...]


def L(w: Word) -> Word:
    return tuple(x - 1 for x in reversed(w))


def R(w: Word) -> Word:
    return tuple(x + 1 for x in reversed(w))


def enumerate_x(max_n: int) -> dict[int, set[Word]]:
    words = {1: {(0,)}}
    for n in range(2, max_n + 1):
        nxt = set()
        for i in range(1, n):
            for u in words[i]:
                for v in words[n - i]:
                    nxt.add(L(u) + v)
                    nxt.add(u + R(v))
        words[n] = nxt
    return words


def catalan(n: int) -> int:
    return comb(2 * n, n) // (n + 1)


def main() -> None:
    max_n = 7
    words = enumerate_x(max_n)
    P = {n: {w for w in words[n] if w.count(0) == 1} for n in range(1, max_n + 1)}
    P[0] = {()}

    print("=== |P_n| vs C_n ===")
    for n in range(1, max_n + 1):
        print(f" n={n}: |P|={len(P[n])} C_n={catalan(n)}")

    print("=== L(p)++[0]++R(q) over all P_i x P_j ===")
    for n in range(1, max_n + 1):
        built = set()
        extra = []
        for i in range(n):
            j = n - 1 - i
            for p in P[i]:
                for q in P[j]:
                    w = L(p) + (0,) + R(q)
                    if w in P[n]:
                        built.add(w)
                    else:
                        extra.append((p, q, w))
        missing = P[n] - built
        print(
            f" n={n}: built_in_P={len(built)} |P|={len(P[n])} "
            f"missing={len(missing)} extra={len(extra)} "
            f"e.g. miss={list(missing)[:2]} extra={extra[:2]}"
        )

    print("=== restrict: p ends with 0 (no +1), q starts with 0 (no -1) ===")
    for n in range(1, max_n + 1):
        built = set()
        extra = []
        for i in range(n):
            j = n - 1 - i
            lefts = {p for p in P[i] if i == 0 or p[-1] == 0}
            rights = {q for q in P[j] if j == 0 or q[0] == 0}
            for p in lefts:
                for q in rights:
                    w = L(p) + (0,) + R(q)
                    if len(w) != n:
                        continue
                    if w in P[n]:
                        built.add(w)
                    else:
                        extra.append((p, q, w))
        missing = P[n] - built
        print(
            f" n={n}: |lefts-rights built|={len(built)} |P|={len(P[n])} "
            f"missing={len(missing)} extra={len(extra)} "
            f"miss={sorted(missing)[:3]} extra={extra[:2]}"
        )

    print("=== first-return: shortest right peel of the P-word itself ===")
    by_len = words

    def right_parses(w: Word):
        n = len(w)
        out = []
        for i in range(1, n):
            pre, suf = w[:i], w[i:]
            vv = L(suf)
            if pre in by_len[i] and vv in by_len[n - i]:
                out.append((pre, vv))
        return out

    for n in range(2, max_n + 1):
        no_r = 0
        peel_p = 0
        peel_not_p = 0
        for w in P[n]:
            rp = right_parses(w)
            if not rp:
                no_r += 1
                continue
            m = min(len(v) for _, v in rp)
            hits = [(u, v) for u, v in rp if len(v) == m]
            u, v = hits[0]
            if v in P[n - len(u)] or v in P[len(v)]:
                peel_p += 1
            else:
                peel_not_p += 1
        print(f" n={n}: noR={no_r} shortest_remainder_in_P={peel_p} notP={peel_not_p}")

    print("=== constructors of P-words: left vs right, factor P? ===")
    for n in range(2, max_n + 1):
        stats = {
            "left_rightP": 0,
            "right_leftP": 0,
            "left_any": 0,
            "right_any": 0,
            "both": 0,
        }
        for w in P[n]:
            lefts = []
            rights = []
            for i in range(1, n):
                pre, suf = w[:i], w[i:]
                u = R(pre)
                if u in by_len[i] and suf in by_len[n - i]:
                    lefts.append((u, suf))
                vv = L(suf)
                if pre in by_len[i] and vv in by_len[n - i]:
                    rights.append((pre, vv))
            if lefts:
                stats["left_any"] += 1
                if any(suf in P[len(suf)] for _, suf in lefts):
                    stats["left_rightP"] += 1
            if rights:
                stats["right_any"] += 1
                if any(pre in P[len(pre)] for pre, _ in rights):
                    stats["right_leftP"] += 1
            if lefts and rights:
                stats["both"] += 1
        print(f" n={n}: {stats} |P|={len(P[n])}")

    print("=== idx hist vs C_k C_{n-1-k} ===")
    for n in range(1, max_n + 1):
        hist = {k: sum(1 for w in P[n] if w.index(0) == k) for k in range(n)}
        pred = {k: catalan(k) * catalan(n - 1 - k) for k in range(n)}
        print(f" n={n}: hist={hist} pred={pred} match={hist == pred}")

    print("=== P_n start-with-0 vs P_{n-1} candidate maps ===")
    for n in range(2, max_n + 1):
        S = {w for w in P[n] if w[0] == 0}
        T = P[n - 1]
        maps = {
            "drop0": lambda w: w[1:],
            "drop0_sub1": lambda w: tuple(x - 1 for x in w[1:]),
            "L_tail": lambda w: L(w[1:]),
            "Rinv_tail": lambda w: L(w[1:]),
            "drop_last": lambda w: w[:-1],
            "drop_last_sub1": lambda w: tuple(x - 1 for x in w[:-1]) if w[:-1] else (),
            "rho_drop0": lambda w: tuple(-x for x in reversed(w[1:])),
        }
        for name, fn in maps.items():
            image = []
            ok = True
            for w in S:
                try:
                    image.append(fn(w))
                except Exception:
                    ok = False
                    break
            if not ok:
                print(f" n={n} {name}: failed")
                continue
            ims = set(image)
            print(
                f" n={n} {name}: |S|={len(S)} |im|={len(ims)} inj={len(image)==len(ims)} "
                f"im_in_P={ims <= T} im==P={ims == T} extra={list(ims - T)[:2]} "
                f"miss={list(T - ims)[:2]}"
            )

    print("=== glue take++[0] and 0::drop is inverse ===")
    for n in range(1, max_n + 1):
        bad = 0
        for w in P[n]:
            k = w.index(0)
            left = w[:k] + (0,)
            right = (0,) + w[k + 1 :]
            if left not in P[k + 1] or right not in P[len(right)]:
                bad += 1
            recon = left[:-1] + right
            if recon != w:
                bad += 1
            # also left ends 0, right starts 0
            if left[-1] != 0 or right[0] != 0:
                bad += 1
        print(f" n={n}: split_bad={bad}")


if __name__ == "__main__":
    main()
