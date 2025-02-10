import Mathlib

namespace easy_9

open Finset
/--
The father has six sons and ten identical, indistinguishable balls. How many ways can he give the balls to his sons if everyone gets at least one?
-/
theorem easy_9 :
  {(f : (Multiset.replicate 10 (1 : ℕ)) → range 6) | ∀ y : range 6, ∃ x, f x = y}.ncard = 126 := by
    sorry
