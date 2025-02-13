import Mathlib

open Finset
/--
The father has six sons and ten identical, indistinguishable balls. How many ways can he give the balls to his sons if everyone gets at least one?
-/
theorem easy_9 (sols : Finset (Fin 6 → ℕ))
    (h_sols : ∀ f, f ∈ sols ↔ ((∀ i, f i > 0) ∧ (∑ i, f i = 10))) :
    sols.card = 126 := by sorry
