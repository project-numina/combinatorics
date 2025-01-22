import Mathlib


open Finset
/--
How many different ways can three people divide seven pears and five apples?
-/
theorem easy_10 : {(f : (Multiset.replicate 7 (1 : ℕ)) → range 3) | 1 = 1}.ncard *
    {(f : (Multiset.replicate 5 (1 : ℕ)) → range 3) | 1 = 1}.ncard = 756 := by
    sorry
