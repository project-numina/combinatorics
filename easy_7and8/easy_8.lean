import Combinatorics.PermutationsCombinations.Combinations


/--
A ferry with a capacity of 10 people takes a group of 13 men and 7 women across a river.
  Find the number of waysin which the qroup may be taken across the if all women go on the first group.
  -/
theorem easy_8 (s t : ℕ) :
 ((Finset.powersetCard s ((Finset.range 7))).filter fun s ↦ s.card = 7).card *
  ((Finset.powersetCard t ((Finset.range 13))).filter fun t ↦ s + t.card = 10 ∧ s = 7).card = 286 := by sorry
