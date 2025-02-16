import Mathlib

/--
How many ways can a teacher select a group of 6 students to sit in the front row if the class has 13 students?
-/
theorem easy_1 (sols : Finset (Fin 13 → Fin 2))
    (h_sols : ∀ f, f ∈ sols ↔ ((List.ofFn f).count 0 = 6)) :
    sols.card = 1716 := by
  sorry
