import Combinatorics.MyMulset
import Combinatorics.PermutationsCombinations.Permutations

open List Finset Nat

/--
There are 8 athletes participating in a sprint competition. The referee needs to select 3 athletes and assign them specific rankings (first place, second place, and third place). How many different arrangements are possible?
-/
theorem case_12_v1 : (Finset.permutationsLength 3 (range 8)).card = 336 := by
  rw [permutationsLength_card] <;> aesop
  

/--
The group of 10 girls should be divided into two groups with at least four girls in each group. How many ways can this be done?
-/
theorem easy_7 (x y : ℕ) :
 ((powersetCard x ((range 10))).filter fun x ↦ x.card + y = 10 ∧ x.card ≥ 4 ∧ y ≥ 4).card = 462 := by sorry



/--
A ferry with a capacity of 10 people takes a group of 13 men and 7 women across a river.
  Find the number of waysin which the qroup may be taken across the if all women go on the first group.
  -/
theorem easy_8 (s t : ℕ) :
 ((powersetCard s ((range 7))).filter fun s ↦ s.card = 7).card * ((powersetCard t ((range 13))).filter fun t ↦ s + t.card = 10 ∧ s = 7 ).card= 286 := by sorry
