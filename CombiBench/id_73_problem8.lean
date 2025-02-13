import Combinatorics.MyMultiset.Comb

/-
Determine the total number of combinations (of any size) of a multiset of objects of $k$ different types with finite repetition numbers $n_{1}, n_{2}, \ldots, n_{k}$, respectively.
-/

-- here nᵢ represents is the number of objects of type i
-- so a combination is just another function `f : Fin k → ℕ` representing how many objects of each type are in the combination
-- since `f` is a subset, we need `f i ≤ n i` for all `i`
example {k : ℕ} (n : Fin k → ℕ)
    (sols : Finset (Fin k → ℕ))
    (h_sols : ∀ f, f ∈ sols ↔ (∀ i, f i ≤ n i)) :
    sols.card =
    ∑ i : Fin k, (n i + 1) := by
  sorry
