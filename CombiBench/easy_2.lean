import Mathlib

/--
There are 8 athletes participating in a sprint competition. The referee needs to select 3 athletes and assign them specific rankings (first place, second place, and third place). How many different arrangements are possible?
-/
theorem easy_2 (sols : Finset (Fin 8 → Fin 4))
    (h_sols : ∀ f, f ∈ sols ↔
    (((@Finset.univ (Fin 8)).filter (fun i => f i = 0)).card = 1) ∧
    (((@Finset.univ (Fin 8)).filter (fun i => f i = 1)).card = 1) ∧
    (((@Finset.univ (Fin 8)).filter (fun i => f i = 2)).card = 1)) :
    sols.card = 336 := by
  sorry
