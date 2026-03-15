# Erdős Problem 647

## The Question

Let $\tau(n)$ count the number of divisors of $n$.  
Is there some $n > 24$ such that

$$\max_{m < n}\bigl(m + \tau(m)\bigr) \leq n + 2\,?$$

This question appears in Erdős's list of unsolved problems in number theory.

---

## Setup and Notation

Define
$$f(m) = m + \tau(m), \qquad g(N) = \max_{m \leq N} f(m) \quad \text{(running maximum)}.$$

The condition becomes: $g(n-1) \leq n + 2$.

**Key quantity — the deficit:**
$$\delta(n) = g(n-1) - n$$

We want $\delta(n) \leq 2$ for some $n > 24$.

### Dynamics of $\delta$

- If $m = n-1$ sets a new record (i.e., $f(n-1) > g(n-2)$), then  
  $\delta(n) = f(n-1) - n = \tau(n-1) - 1.$
- Otherwise $g(n-1) = g(n-2)$, so $\delta(n) = \delta(n-1) - 1$ (decreases by 1).

Thus $\delta$ decreases linearly between record events and **resets to $\tau(m)-1$** when $m$ sets a new record.

---

## Known Baseline: n = 24

The values $m + \tau(m)$ for $m < 24$ are maximized at
$$f(20) = 20 + 6 = 26 = 24 + 2, \quad f(22) = 22 + 4 = 26 = 24 + 2.$$

So $g(23) = 26 = 24 + 2$, confirming $n = 24$ satisfies the condition exactly.

---

## Computational Results

### Search to 5,000,000

```
No n > 24 with δ(n) ≤ 2 found in [25, 5,000,000].
Minimum δ(n) achieved: δ = 3  at  n = 35.
```

At $n = 35$: $g(34) = 38$ (set by $f(30) = 30 + \tau(30) = 30 + 8 = 38$),
and $38 - 35 = 3 > 2$.

### Why δ never drops below 3 (empirically)

Every time $\delta$ approaches 3, a new highly-composite-type record fires.
For example:

| Record-setter $m$ | $\tau(m)$ | $f(m)$ | $\delta$ reset |
|------------------:|----------:|-------:|--------------:|
|  24               | 8         | 32     | 7             |
|  30               | 8         | 38     | 7             |
|  36               | 9         | 45     | 8             |
| 120               | 16        | 136    | 15            |
| 360               | 24        | 384    | 23            |
| 720               | 30        | 750    | 29            |
| 5040              | 60        | 5100   | 59            |

The record-setters are (super)abundant / highly composite numbers, where
$\tau(m)$ grows unboundedly. Because highly composite numbers are denser than
the "decay rate" of $\delta$, the deficit never drops to 2.

### Growth of g(n)

| n         | g(n)      | excess = g(n)−n |
|----------:|----------:|----------------:|
| 100       | 109       | 9               |
| 1,000     | 1,016     | 16              |
| 10,000    | 10,032    | 32              |
| 100,000   | 100,056   | 56              |
| 1,000,000 | 1,000,063 | 63              |

The excess $g(n) - n$ grows like $O(\log n \cdot \log\log n)$
(roughly the maximum of $\tau$ near $n$), which means $\delta(n)$ grows
without bound — the condition $\delta \leq 2$ becomes harder to satisfy as $n$
grows, not easier.

---

## Mathematical Heuristic

The largest $\tau(m)$ for $m \leq N$ is $\Theta\!\left(N^{c/\log\log N}\right)$
for a constant $c$, meaning $g(N) - N \to \infty$ as $N \to \infty$.

Between consecutive record-setters $m_1 < m_2$, $\delta$ decreases by 1 per
step, going from $\tau(m_1) - 1$ down to roughly
$$\tau(m_1) - 1 - (m_2 - m_1 - 1) = \tau(m_1) - (m_2 - m_1).$$
For $\delta$ to reach 2, we need a gap $m_2 - m_1 > \tau(m_1) - 3$.
Highly composite numbers have large $\tau$ **and** small gaps between them,
making such a drop impossible in practice.

---

## Conclusion

Computational evidence strongly suggests that **$n = 24$ is the last solution**.
While no proof is known, the behavior of $\delta(n)$ — whose floor is 3 for
all checked $n \in (24, 5 \times 10^6]$ — supports the conjecture that no
$n > 24$ satisfies the condition.

---

## Files

| File | Description |
|------|-------------|
| `search.py` | Main sieve-based search up to any limit |
| `analysis.py` | Records, δ-trajectory, and growth analysis |
| `results.txt` | Output of `search.py --limit 5000000 --verbose` |
| `analysis_results.txt` | Output of `analysis.py --limit 1000000` |
| `lean/Erdos647.lean` | Lean 4 formal verification (see below) |

## Lean 4 Formal Proof

The `lean/` subdirectory contains a Lean 4 formalization using Mathlib.

### What is proved (no `sorry`)

| Theorem | Statement |
|---------|-----------|
| `tau_24` | τ(24) = 8 |
| `runningMax_24` | max_{m<24} f(m) = 26 |
| `delta_24` | δ(24) = 2 |
| `n24_satisfies` | n = 24 satisfies the condition |
| `solutions_le_24` | Exact solution set below 25: {0,1,2,3,4,5,6,8,10,12,24} |
| `f_le_runningMax` | f(m) ≤ runningMax(n) whenever m < n |
| `no_solution_25_to_500` | No n ∈ [25, 500] satisfies the condition |
| `delta_ge_three_25_to_500` | δ(n) ≥ 3 for all n ∈ [25, 500] |
| `not_satisfies_35/48/61` | Explicit witness certificates |
| `growth_of_delta` | δ(100)=8, δ(1000)=14, δ(10000)=32 |
| `erdos_647_partial` | No solution in (24, 500] |

### What remains open (`sorry`)

```
theorem erdos_647_conjecture : ∀ n : ℕ, n > 24 → ¬satisfiesErdos647 n
```

Computationally verified to 5,000,000 but no mathematical proof is known.

### Build instructions

```bash
cd lean
lake update   # fetch Mathlib (uses cached .olean files if available)
lake build    # type-checks all theorems; ~2 min with cache
```

Requires: [elan](https://github.com/leanprover/elan) + toolchain `leanprover/lean4:v4.29.0-rc6`.

## Usage

```bash
# Search up to 10 million
python3 search.py --limit 10000000

# Analyse delta dynamics up to 1 million
python3 analysis.py --limit 1000000
```

Requires Python 3.6+ (standard library only).
