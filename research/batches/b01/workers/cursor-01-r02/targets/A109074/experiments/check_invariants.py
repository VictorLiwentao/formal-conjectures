#!/usr/bin/env python3
"""Check P/R/U induction quantities and floor-delta d(r,Q).

Not a proof. Used to select a Lean induction invariant.
"""
from collections import Counter


def pop(x: int) -> int:
    return bin(x).count("1")


def prefix(n: int):
    S = A = B = C = 0
    for k in range(n):
        S += pop(k)
        A += pop(3 * k)
        B += pop(3 * k + 1)
        C += pop(3 * k + 2)
    P = S + n - C
    R = S + n - B
    U = S + n - A
    return S, A, B, C, P, R, U


def d(r: int, Q: int) -> int:
    return (3 * r + 1) // Q - (2 * r + 1) // Q - (2 * r) // Q


def main() -> None:
    minP = minR = minU = 10**9
    min_dP = min_dR = min_dU = 10**9
    min_crude = 10**9
    worst = []
    for m in range(0, 4096):
        _, _, _, _, P, R, U = prefix(m)
        minP, minR, minU = min(minP, P), min(minR, R), min(minU, U)
        popm = pop(m)
        dP = P + R + 1 + popm - pop(3 * m + 1)
        dR = P + U + popm - pop(3 * m)
        dU = R + U + 1 + popm - pop(3 * m)
        min_dP, min_dR, min_dU = min(min_dP, dP), min(min_dR, dR), min(min_dU, dU)
        min_crude = min(min_crude, P + R - popm)
        if min(dP, dR, dU) < 0:
            worst.append((m, P, R, U, dP, dR, dU))
    print("min P,R,U on [0,4096)", minP, minR, minU)
    print("min odd-step deltas dP,dR,dU", min_dP, min_dR, min_dU)
    print("min crude P+R-pop", min_crude)
    print("negative odd-step count", len(worst), "first", worst[:5])

    print("d(r,Q) value sets:")
    for Q in [2, 3, 4, 5, 6, 7, 8, 9, 16, 25, 27, 32]:
        vals = [d(r, Q) for r in range(Q)]
        print(Q, Counter(vals), "sum", sum(vals))

    # two-adic prefix using odds only
    s = 0
    mn = 0
    for n in range(1, 4097):
        s += pop(2 * n - 1) - pop(6 * n - 2)
        mn = min(mn, s)
    print("two_adic_prefix_min_n_le_4096", mn)

    # odd-prime digit-sum prefixes
    def s_p(p, x):
        if x == 0:
            return 0
        t = 0
        while x:
            t += x % p
            x //= p
        return t

    for p in [3, 5, 7, 11, 13]:
        s = 0
        mn = 0
        for n in range(1, 801):
            s += (
                s_p(p, 4 * n - 1)
                + s_p(p, 4 * n - 2)
                - s_p(p, 6 * n - 2)
                - s_p(p, 2 * n - 1)
            )
            mn = min(mn, s)
        print(f"odd_p_prefix_min p={p} n<=800", mn)


if __name__ == "__main__":
    main()
