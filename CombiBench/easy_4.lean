import Mathlib

abbrev easy_4_solution : ℕ := sorry

/--
A restaurant’s menu has 3 appetizers, 3 mains and 2 desserts. In how many way can a 3-course meal be ordered?
-/
theorem easy_4 : Fintype.card (Fin 3 × Fin 3 × Fin 2) = easy_4_solution := by sorry
