/-
Determine the total number of combinations (of any size) of a multiset of objects of $k$ different types with finite repetition numbers $n_{1}, n_{2}, \ldots, n_{k}$, respectively.
-/

import Combinatorics.MyMultiset.Comb

namespace id_73_problem8

variable {k : ℕ} (n : Fin k → ℕ)

def S : MyMultiset (Fin k) where
  rep := (↑) ∘ n

instance : (S n).RepIsFinite where
  rep_finite i := by simp [S]

example :
    ∑ i ∈ Finset.range ((S n).card + 1), Fintype.card ((S n).Comb i) = ∑ i : Fin k, (n i + 1) := by
  sorry

end id_73_problem8
