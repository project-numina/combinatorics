import Mathlib

open Finset
/--
How many different ways can three people divide seven pears and five apples?
-/
theorem easy_10 (sols : Finset (Fin 3 → (ℕ × ℕ)))
    (h_sols : ∀ f, f ∈ sols ↔ (∑ i, (f i).1 = 7 ∧ ∑ i, (f i).2 = 5)) :
    sols.card = 756 := by
  sorry
