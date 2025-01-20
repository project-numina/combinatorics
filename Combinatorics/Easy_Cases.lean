import Combinatorics.MyMulset
import Combinatorics.PermutationsCombinations.Permutations

open List Finset

/--
There are 8 athletes participating in a sprint competition. The referee needs to select 3 athletes and assign them specific rankings (first place, second place, and third place). How many different arrangements are possible?
-/
theorem case_12_v1: (Finset.permutationsLength 3 (range 8)).card = 336 := by
  rw [permutationsLength_card] <;> aesop
