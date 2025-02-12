import Combinatorics.PermutationsCombinations.Combinations

/--
The group of 10 girls should be divided into two groups with at least four girls in each group. How many ways can this be done?
-/
theorem easy_7 (x y : ℕ) :
 ((Finset.powersetCard x ((Finset.range 10))).filter fun x ↦ x.card + y = 10 ∧
  x.card ≥ 4 ∧ y ≥ 4).card = 462 := by sorry
