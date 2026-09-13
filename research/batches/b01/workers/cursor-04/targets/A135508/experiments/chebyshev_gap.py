#!/usr/bin/env python3
"""Elementary Chebyshev product bound for the leftover injector window.

Experimental / analytic note, not a Lean proof.

If every admissible k ≡ 5 (mod 6) with 5 ≤ k ≤ q+6 made kq-2 a q-smooth
composite, the product Π = ∏ (kq-2) would be q-smooth. Mathlib supplies
θ(x) ≤ (log 4) x. Abel summation then bounds ∑_{p≤q} (log p)/p by
(log 4) log q. The resulting upper bound on log Π is about
(q/6)(log 4) log q + O(q), while the terms themselves give
log Π ≥ (q/3) log q - O(q). The logarithmic gap is about 0.102 q log q
versus an O(q) extra from e_max. That only contradicts smoothness once
log q ≳ 30, i.e. q ≳ 10^13, which is not a Lean-checkable complementary
range. A Mertens-quality ∑ (log p)/p ~ log q still leaves an O(q) extra
and does not close the leftover window at q ≥ 113.

This script prints the numerical gap at leftover q and at 10^6.
"""

from __future__ import annotations

import math


def gap(q: int) -> dict[str, float]:
    n = (q + 7) / 6
    logq = math.log(q)
    lower = (q / 3) * logq - q
    upper_main = (q / 6) * math.log(4) * logq
    extra = 2 * math.log(4) * q + 3 * q ** (2 / 3)
    return {
        "q": q,
        "n_candidates": n,
        "lower": lower,
        "upper_main": upper_main,
        "extra": extra,
        "upper": upper_main + extra,
        "signed_gap_lower_minus_upper": lower - (upper_main + extra),
    }


def main() -> None:
    for q in (113, 163, 227, 257, 40973, 10**6, 10**9, 10**13, 10**15):
        g = gap(q)
        print(
            f"q={q:<12} lower-upper={g['signed_gap_lower_minus_upper']:.3e} "
            f"lower={g['lower']:.3e} upper={g['upper']:.3e}"
        )


if __name__ == "__main__":
    main()
