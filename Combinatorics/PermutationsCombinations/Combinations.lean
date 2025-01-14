import Mathlib.Data.Finset.Powerset
import Combinatorics.PermutationsCombinations.Permutations

open Nat Finset

/-- Generate all possible subsets of size k from a given finite set s .
-/
def combinations (r : ℕ) (s : Finset α) : Finset (Finset α) :=
  s.powersetCard r

theorem combinations_card (r : ℕ) (s : Finset α) :
  s.card.choose r = (combinations r s).card := by
    rw [combinations]
    exact (Finset.card_powersetCard r s).symm

/--
Theorem 2.3.1 For 0 ≤ r ≤ n, P(n, r) = r! × C(n, r). Hence, C(n, r) = n! / (r! × (n - r)!).
-/
theorem  combinations_Factorial  (r : ℕ) (s : Finset α) (h : r ≤ s.card) (hp: (permutationsLength r s).card = r.factorial * (combinations r s).card) :
  (combinations r s).card = (Finset.card s).factorial / (r.factorial * (Finset.card s - r).factorial) := by sorry


/-
  Corollary 2.3.2 For 0 ≤ r ≤ n, C(n, n - k) = C(n, k)
-/
-- This theorem has already been formalized in Mathlib under the name Nat.choose_symm.


/--
  Theorem 2.3.3 (Pascal's formula) For all integers n and k with 1 ≤ k ≤ n - 1, C(n, k) = C(n - 1, k - 1) + C(n - 1, k).
-/
theorem Pascal_formula {n k : ℕ} (hk1 : 1 ≤ k)(hkn : k ≤ n - 1) :
  choose n k = choose (n - 1) (k - 1) + choose (n - 1) k := by
  rw [Nat.choose_eq_choose_pred_add (show 0 < n by omega) (show 0 < k by omega)]



/-
  Theorem 2.3.4 For n ≥ 0, C(n, 0) + C(n, 1) + ... + C(n, n) = 2^n.
-/
-- This theorem has already been formalized in Mathlib under the name Nat.sum_range_choose.
