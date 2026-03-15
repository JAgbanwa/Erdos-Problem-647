"""
Erdős Problem 647 — Delta Dynamics Analysis
=============================================

Examines how δ(n) = max_{m<n}(m+τ(m)) - n behaves.

Key observations:
  - When m is a highly-composite-like number, τ(m) is large,
    causing δ to spike.
  - δ decreases by 1 for each n that doesn't set a new record.
  - For a solution n>24 to exist, δ must drop to ≤2 before
    the next large τ spike occurs.

This script prints:
  1. Record setters: m where f(m) = m+τ(m) exceeds all prior values.
  2. The δ trajectory and the "close calls" (minimum δ per decade).
"""

import time
from array import array


def sieve_tau(N: int) -> array:
    tau = array('I', [0] * (N + 1))
    for d in range(1, N + 1):
        for multiple in range(d, N + 1, d):
            tau[multiple] += 1
    return tau


def analyze(limit: int = 1_000_000):
    print(f"Analyzing up to {limit:,} ...")
    t0 = time.time()
    tau = sieve_tau(limit)
    print(f"Sieve done in {time.time()-t0:.2f}s\n")

    print("=== Record Setters (m where f(m) exceeds all prior f values) ===")
    print(f"{'m':>10}  {'τ(m)':>6}  {'f(m)=m+τ':>10}  {'δ=τ(m)-1':>8}")
    print("-" * 45)

    g = 0
    records = []
    for m in range(1, limit + 1):
        fm = m + tau[m]
        if fm > g:
            g = fm
            records.append((m, tau[m], fm, tau[m] - 1))
            if m <= 10_000 or m % 100_000 == 0:
                print(f"{m:>10}  {tau[m]:>6}  {fm:>10}  {tau[m]-1:>8}")

    print(f"\nTotal records up to {limit:,}: {len(records)}")

    # Delta trajectory: close calls after n=24
    print("\n=== δ Trajectory: closest approaches to δ≤2 after n=24 ===")
    print(f"{'n':>10}  {'g(n-1)':>10}  {'n+2':>8}  {'δ':>5}")
    print("-" * 40)

    g_r = 0
    decade_min = {}  # decade -> (min_delta, n)
    for m in range(1, limit + 1):
        fm = m + tau[m]
        if fm > g_r:
            g_r = fm
        n = m + 1
        if n > 24:
            delta = g_r - n
            decade = n // 1000
            if decade not in decade_min or delta < decade_min[decade][0]:
                decade_min[decade] = (delta, n, g_r)

    for decade in sorted(decade_min.keys())[:50]:  # first 50 decades
        d, n, g_val = decade_min[decade]
        marker = " *** SOLUTION ***" if d <= 2 else ""
        print(f"{n:>10}  {g_val:>10}  {n+2:>8}  {d:>5}{marker}")

    overall_min = min(decade_min.values(), key=lambda x: x[0])
    print(f"\nOverall minimum δ for n>24 in [25, {limit:,}]: "
          f"δ={overall_min[0]} at n={overall_min[1]}")

    # Show growth rate of g vs n
    print("\n=== Growth of g(n) vs n ===")
    checkpoints = [100, 1000, 10000, 100000, 1000000]
    g_r = 0
    for m in range(1, limit + 1):
        fm = m + tau[m]
        if fm > g_r:
            g_r = fm
        if m in checkpoints:
            print(f"  n={m:>8,}: g(n) = {g_r:>10,}  excess = {g_r-m:>6,}  ratio = {g_r/m:.6f}")


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=1_000_000)
    args = parser.parse_args()
    analyze(args.limit)
