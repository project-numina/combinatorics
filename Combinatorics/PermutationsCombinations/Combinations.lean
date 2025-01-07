import Mathlib
import Combinatorics.PermutationsCombinations.permutation


open Nat Finset BigOperators


/-
Theorem 2.3.1 For 0 ≤ r ≤ n, P(n, r) = r! × C(n, r). Hence, C(n, r) = n! / (r! × (n - r)!).
-/
theorem  permutations_choose_Factorial  (r : ℕ) (n : Finset α) (h : r ≤ n.card) (hp: (permutationsLength r n).card = n.card.factorial / (n.card - r).factorial) :
  n.card.choose r = n.card.factorial / (r.factorial * (n.card - r).factorial)  := by sorry

-- theorem  permutations_choose_Factorial'  {n k : ℕ} (hk : k ≤ n) :
--     choose n k = n ! / (k ! * (n - k)!) :=
--   choose_eq_factorial_div_factorial hk


/-
  Corollary 2.3.2 For 0 ≤ r ≤ n, C(n, n - k) = C(n, k)
-/
lemma choose_symm {n k : ℕ} (hk : k ≤ n) : choose n (n - k) = choose n k :=
  Nat.choose_symm hk


/-
  Theorem 2.3.3 (Pascal's formula) For all integers n and k with 1 ≤ k ≤ n - 1, C(n, k) = C(n - 1, k - 1) + C(n - 1, k).
-/

theorem Pascal_formula {n k : ℕ} (hk1 : 1 ≤ k)(hkn : k ≤ n - 1) :
  choose n k = choose (n - 1) (k - 1) + choose (n - 1) k := by

  have hn : 0 < n := by omega
  have hk : 0 < k := by omega
  rw [Nat.choose_eq_choose_pred_add hn hk]

/-
  Theorem 2.3.4 For n ≥ 0, C(n, 0) + C(n, 1) + ... + C(n, n) = 2^n.
-/

theorem sum_range_choose {n : ℕ} : ∑ k in range (n + 1), choose n k  = 2 ^ n :=
  Nat.sum_range_choose n
