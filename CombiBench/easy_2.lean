import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Combinatorics.PermutationsCombinations.Permutations

open Finset

/--
There are 8 athletes participating in a sprint competition. The referee needs to select 3 athletes and assign them specific rankings (first place, second place, and third place). How many different arrangements are possible?
-/
theorem easy_2 : (permutationsLength 3 (@univ (Fin 8) _)).card = 336 := by
  rw [permutationsLength_card]
  . rfl
  . simp
