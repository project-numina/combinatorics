import Mathlib

namespace easy_7

open Finset

/--
The group of 10 girls should be divided into two groups with at least four girls in each group.
-/
theorem easy_7
    (sols : Finset (Fin 2 → ℕ))
    (h_sols : ∀ f, f ∈ sols ↔ ((∀ i, f i ≥ 4) ∧ (∑ i, f i = 10))) :
     sols.card = 462 := by
  sorry

end easy_7
