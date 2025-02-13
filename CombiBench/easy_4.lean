import Mathlib

/--
A restaurant’s menu has 3 appetizers, 3 mains and 2 desserts. In how many way can a 3-course meal be ordered?
-/
theorem easy_4
    (sols : Finset (Fin 3 → ℕ))
    (h_sols : ∀ f, f ∈ sols ↔ (f 0 ≤ 3 ∧ f 1 ≤ 3 ∧ f 2 ≤ 2 ∧ f 0 + f 1 + f 2 = 3)) :
    sols.card = 18 := by sorry
