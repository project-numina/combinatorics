import Mathlib

/--
The group of 10 girls should be divided into two groups with at least four girls in each group. How many ways can this be done?
-/
theorem easy_7
    (sols : Finset (Finpartition (@Finset.univ (Fin 10))))
    (h_sols : ∀ f, f ∈ sols ↔ (f.parts.card = 2) ∧ (∀ i, i ∈ f.parts → i.card ≥ 4)) :
    sols.card = 462 := by
  sorry
