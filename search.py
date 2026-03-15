"""
Erdős Problem 647 — Computational Search
=========================================

Define  f(m) = m + τ(m),  where τ(m) = number of divisors of m.
Define  g(N)  = max_{m ≤ N} f(m)   (running maximum).

We search for n > 24 such that  g(n-1) ≤ n + 2,
i.e. every m < n satisfies  m + τ(m) ≤ n + 2.

Background
----------
n = 24 is a known solution: g(23) = max{f(m): m<24} = f(20) = f(22) = 26 = 24+2.

The question (Erdős) is whether 24 is the LAST such n, or if sporadic larger
solutions exist.

Key quantity
------------
Let δ(n) = g(n-1) - n  ("deficit relative to n").
The condition  g(n-1) ≤ n+2  is equivalent to  δ(n) ≤ 2.

δ decreases by 1 for each consecutive n where no new record is set,
and jumps to τ(n) - 1  whenever f(n) = n + τ(n) > g(n-1).

Usage
-----
    python3 search.py [--limit N] [--verbose]

Default limit: 10_000_000.
"""

import argparse
import time
from array import array

def sieve_tau(N: int) -> array:
    """Return array tau[1..N] where tau[i] = number of divisors of i."""
    tau = array('I', [0] * (N + 1))
    for d in range(1, N + 1):
        for multiple in range(d, N + 1, d):
            tau[multiple] += 1
    return tau


def search(limit: int = 10_000_000, verbose: bool = False):
    print(f"Sieving τ up to {limit:,} ...")
    t0 = time.time()
    tau = sieve_tau(limit)
    print(f"Sieve done in {time.time()-t0:.2f}s")

    # Verify n=24 baseline
    g = 0
    for m in range(1, 24):
        v = m + tau[m]
        if v > g:
            g = v
    assert g == 26, f"Baseline failed: g(23) = {g}, expected 26"
    print(f"Baseline verified: g(23) = {g} = 24+2 ✓\n")

    # Main search: we need g BEFORE adding n+1, i.e. g(n-1)
    g = 0
    prev_g = 0
    solutions = []          # (n, g(n-1), delta)
    delta_min_after24 = 10**9

    # Precompute running max up to limit
    # For each n starting at 2, the condition references g(n-1).
    # We update g with f(n-1) before checking condition for n.

    g_running = 0
    for m in range(1, limit + 1):
        g_before = g_running          # = g(m-1) = max_{i < m} f(i)
        fm = m + tau[m]
        if fm > g_running:
            g_running = fm            # update g(m)

        # n = m+1: check if g(n-1) = g(m) ≤ (m+1)+2 = m+3
        n = m + 1
        if n > 24:
            g_nm1 = g_running         # g(n-1) = g(m)
            delta = g_nm1 - n
            if delta < delta_min_after24:
                delta_min_after24 = delta
                if verbose:
                    print(f"  New min δ: n={n}, g(n-1)={g_nm1}, δ={delta}")
            if delta <= 2:
                solutions.append((n, g_nm1, delta))
                print(f"*** SOLUTION: n={n}, g(n-1)={g_nm1}, n+2={n+2}, δ={delta} ***")

    print(f"\nSearch complete up to n={limit:,}")
    print(f"Solutions found (n>24): {len(solutions)}")
    print(f"Minimum δ(n) achieved for n>24: {delta_min_after24}")

    # Show δ trajectory near the minimum
    if verbose or delta_min_after24 > 2:
        print("\nSample of δ values for early n > 24:")
        g_r = 0
        for m in range(1, min(200, limit) + 1):
            fm = m + tau[m]
            if fm > g_r:
                g_r = fm
            n = m + 1
            if 25 <= n <= 80:
                delta = g_r - n
                cond = " *** SOLUTION ***" if delta <= 2 else ""
                print(f"  n={n:3d}  g(n-1)={g_r:5d}  δ={delta:3d}{cond}")

    return solutions, delta_min_after24


def main():
    parser = argparse.ArgumentParser(description="Erdős Problem 647 search")
    parser.add_argument("--limit", type=int, default=10_000_000,
                        help="Search up to this n (default: 10,000,000)")
    parser.add_argument("--verbose", action="store_true",
                        help="Print δ trajectory")
    args = parser.parse_args()
    search(args.limit, args.verbose)


if __name__ == "__main__":
    main()
