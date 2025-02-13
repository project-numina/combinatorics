import Mathlib


/--
A ferry with a capacity of 10 people takes a group of 13 men and 7 women across a river.
  Find the number of ways in which the group may be taken across the if all women go on the first group.
-/
theorem easy_8
    (sols : Finset (Fin 2 → (ℕ × ℕ)))
    (h_sols : ∀ f, f ∈ sols ↔ (∑ i, (f i).1 = 13 ∧ ∑ i, (f i).2 = 7 ∧ (f 0).2 = 7)) :
    sols.card= 286 := by sorry

 