import Mathlib

namespace easy_7

/--
The group of 10 girls should be divided into two groups with at least four girls in each group.
-/
theorem easy_7
    (sols : Finset (Finpartition (@Finset.univ (Fin 10))))
    (h_sols : ∀ f, f ∈ sols ↔ (f.parts.card = 2) ∧ (∀ i, i ∈ f.parts → i.card ≥ 4)) :
    sols.card = 462 := by sorry

end easy_7
