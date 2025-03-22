import Mathlib

abbrev easy_3_solution : ℕ := sorry

/--
How many four-digit numbers can be formed from the numbers 3 5 8 9 if they are not allowed to be repeated?
-/
theorem easy_3 (sol : Finset ℕ)
    (h_sol : ∀ s ∈ sol, 1000 ≤ s ∧ s ≤ 9999 ∧ (Nat.digits 10 s).toFinset = {3, 5, 8, 9}) :
    sol.card = easy_3_solution := by sorry
