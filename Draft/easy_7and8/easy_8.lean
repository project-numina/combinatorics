import Mathlib


/--
A ferry with a capacity of 10 people takes a group of 13 men and 7 women across a river.
  Find the number of ways in which the group may be taken across the if all women go on the first group.
-/
theorem easy_8
    (sols : Finset ((Fin 13 → Fin 2) × (Fin 7 → Fin 2)))
    (h_women : ∀ f ∈ sols, ∀ i, f.2 i = 0)
    (h_sols : ∀ f, f ∈ sols ↔ ((@Finset.univ (Fin 13)).filter (fun i => f.1 i = 0)).card = 3) :
    sols.card= 286 := by
  sorry 
