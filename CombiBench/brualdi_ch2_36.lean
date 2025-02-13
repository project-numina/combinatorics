import Combinatorics.MyMultiset.Comb

<<<<<<< HEAD:CombiBench/id_73_problem8.lean
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
=======
variable {k : ℕ} (n : Fin k → ℕ)

def S : MyMultiset (Fin k) where
  rep := (↑) ∘ n

instance : (S n).RepIsFinite where
  rep_finite i := by simp [S]
/--
Determine the total number of combinations (of any size) of a multiset of objects of $k$ different types with finite repetition numbers $n_{1}, n_{2}, \ldots, n_{k}$, respectively.
-/
theorem brualdi_ch2_36 :
    ∑ i ∈ Finset.range ((S n).card + 1), Fintype.card ((S n).Comb i) = ∑ i : Fin k, (n i + 1) := by
>>>>>>> acd312735ba3a8d8200d88860d31584297082f8e:CombiBench/brualdi_ch2_36.lean
  sorry
