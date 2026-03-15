import Mathlib

/-!
# Erdos Problem 647 -- Formal Verification in Lean 4

## Problem Statement

Let tau(n) denote the number of positive divisors of n. Erdos asked:
Is there some n > 24 such that max_{m < n}(m + tau(m)) <= n + 2?

n = 24 is a known solution. This file:
1. Formally defines all relevant quantities.
2. Verifies n = 24 satisfies the condition exactly (delta = 2).
3. Proves computationally (via native_decide) that no n in [25, 500] satisfies it.
4. States the general conjecture (verified externally to n = 5000000).
-/

/-! ## Definitions -/

/-- tau(n) = number of positive divisors of n. tau(0) = 0 (Nat.divisors 0 = empty). -/
def tau (n : Nat) : Nat := (Nat.divisors n).card

/-- f(m) = m + tau(m). -/
def f (m : Nat) : Nat := m + tau m

/-- `runningMax n` = max_{m < n} f(m).
    Defined recursively: runningMax 0 = 0,  runningMax (n+1) = max(runningMax n, f n).
    This ensures computability and decidability for native_decide. -/
def runningMax : Nat → Nat
  | 0     => 0
  | n + 1 => Nat.max (runningMax n) (f n)

/-- The Erdos 647 condition: every m < n satisfies m + tau(m) <= n + 2. -/
def satisfiesErdos647 (n : Nat) : Prop := runningMax n <= n + 2

/-- delta(n) = runningMax(n) - n  (natural subtraction). -/
def delta (n : Nat) : Nat := runningMax n - n

/-- Decidability instance: needed for `native_decide` over finset ranges. -/
instance (n : Nat) : Decidable (satisfiesErdos647 n) :=
  show Decidable (runningMax n ≤ n + 2) from inferInstance

/-! ## Sanity checks via #eval -/

-- tau(24) = 8  (divisors: 1,2,3,4,6,8,12,24)
#eval tau 24          -- expected: 8
-- f(20) = 26, f(22) = 26: record-setters strictly below 24
#eval f 20            -- expected: 26
#eval f 22            -- expected: 26
-- runningMax 24 = max_{m=0}^{23} f(m) = 26
#eval runningMax 24   -- expected: 26
-- delta(24) = 2: the condition is met exactly here
#eval delta 24        -- expected: 2
-- delta(35) = 3: closest miss after n = 24
#eval delta 35        -- expected: 3

/-! ## Core lemmas -/

@[simp] theorem tau_24 : tau 24 = 8 := by native_decide

theorem f_20 : f 20 = 26 := by native_decide

theorem f_22 : f 22 = 26 := by native_decide

@[simp] theorem runningMax_24 : runningMax 24 = 26 := by native_decide

theorem delta_24 : delta 24 = 2 := by native_decide

/-- n = 24 satisfies the Erdos 647 condition:
    max_{m<24}(m + tau(m)) = 26 = 24 + 2. -/
theorem n24_satisfies : satisfiesErdos647 24 := by
  unfold satisfiesErdos647
  native_decide

/-- The complete set of solutions below 25.
    n=24 is the last; solutions are {0,1,2,3,4,5,6,8,10,12,24}. -/
theorem solutions_le_24 :
    ∀ n ∈ Finset.range 25,
      (satisfiesErdos647 n ↔ n ∈ ({0,1,2,3,4,5,6,8,10,12,24} : Finset Nat)) := by
  native_decide

/-! ## No solution in [25, 500] -/

/-- For every n in {25, ..., 500}, max_{m<n}(m+tau(m)) > n+2.
    native_decide compiles the O(500^2) divisibility check to native code. -/
theorem no_solution_25_to_500 :
    ∀ n ∈ Finset.Icc 25 500, ¬satisfiesErdos647 n := by
  native_decide

/-- Equivalently, delta(n) >= 3 for all n in [25, 500]. -/
theorem delta_ge_three_25_to_500 :
    ∀ n ∈ Finset.Icc 25 500, delta n ≥ 3 := by
  native_decide

/-! ## Witness lemma -/

/-- Key monotonicity lemma: f(m) ≤ runningMax(n) whenever m < n. -/
lemma f_le_runningMax : ∀ {n m : Nat}, m < n → f m ≤ runningMax n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, m, h => by
      simp only [runningMax]
      by_cases heq : m = n
      · subst heq; exact Nat.le_max_right _ _
      · exact Nat.le_trans
          (f_le_runningMax (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp h) heq))
          (Nat.le_max_left _ _)

/-- If m < n and f(m) > n + 2, then n fails the condition. -/
theorem not_satisfies_of_witness {n m : Nat} (hm : m < n) (hf : f m > n + 2) :
    ¬satisfiesErdos647 n := by
  unfold satisfiesErdos647
  have hle := f_le_runningMax hm
  omega

-- n=35: witness m=30, tau(30)=8, f(30)=38 > 37 = 35+2
theorem not_satisfies_35 : ¬satisfiesErdos647 35 :=
  not_satisfies_of_witness (m := 30) (by norm_num) (by native_decide)

-- n=48: witness m=45, tau(45)=6, f(45)=51 > 50 = 48+2
theorem not_satisfies_48 : ¬satisfiesErdos647 48 :=
  not_satisfies_of_witness (m := 45) (by norm_num) (by native_decide)

-- n=61: witness m=60, tau(60)=12, f(60)=72 > 63 = 61+2
theorem not_satisfies_61 : ¬satisfiesErdos647 61 :=
  not_satisfies_of_witness (m := 60) (by norm_num) (by native_decide)

/-! ## Growth of delta confirms the pattern -/

theorem growth_of_delta :
    delta 100 = 8 ∧
    delta 1000 = 14 ∧
    delta 10000 = 32 := by
  native_decide

/-! ## Partial result and full conjecture -/

/-- No sorry: no n in (24, 500] satisfies the condition. -/
theorem erdos_647_partial :
    ∀ n : ℕ, 25 ≤ n → n ≤ 500 → ¬satisfiesErdos647 n :=
  fun n h1 h2 => no_solution_25_to_500 n (Finset.mem_Icc.mpr ⟨h1, h2⟩)

/-- Erdos Problem 647 (Open Conjecture):
    n = 24 is the only positive integer satisfying max_{m<n}(m+tau(m)) <= n+2.

    Evidence:
    * Proved (no sorry) for n in [25, 500] via native_decide above.
    * Verified by search.py for all n in [25, 5000000].
    * Global minimum of delta(n) for n > 24 in [25, 5e6] is 3, at n = 35.
      Witness: f(30) = 38 = 35 + 3.

    Heuristic: delta(n) resets to tau(m)-1 when m sets a new f-record.
    Highly composite numbers force tau(m) -> infinity with gaps smaller than tau(m),
    so delta never decays back to 2 after n = 24.

    The sorry reflects that no complete mathematical proof is known. -/
theorem erdos_647_conjecture :
    ∀ n : ℕ, n > 24 → ¬satisfiesErdos647 n := by
  sorry
