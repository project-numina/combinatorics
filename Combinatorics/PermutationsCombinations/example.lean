import Mathlib.Data.Nat.Choose.Sum


open Nat

open Finset

open BigOperators


example {m n : ℕ} :
   ∑ k in range (m + 1), choose (n + k) k = choose (n + m + 1) m := by
   induction m with
   | zero =>
    simp only [zero_add, range_one, sum_singleton,
    add_zero, choose_zero_right]

   | succ m IH =>
    rw [sum_range_succ]
    simp only [IH]
    rw [choose_succ_succ]
    simp only [succ_eq_add_one, add_left_inj]
    ring_nf
