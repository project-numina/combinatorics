import Mathlib

/-- 1087
Find the smallest positive integer $n$ such that if $n$ squares of a $1000 \\times 1000$ chessboard are colored, then there will exist three colored squares whose centers form a right triangle with sides parallel to the edges of the board.
-/
theorem usamo_2000_p4
  (sols : Finset (Fin 1000 × Fin 1000))
  (h_sols : ∃ (a b c : (Fin 1000 × Fin 1000)), a ∈ sols ∧ b ∈ sols ∧ c ∈ sols ↔ ((a.1 = b.1 ∧ a.2 = c.2 ∨ a.1 = c.1 ∧ a.2 = b.2) ∧ (a ≠ b ∧ a ≠ c ∧ b ≠ c)))
  : 1999 ≤ sols.card := by
  sorry
