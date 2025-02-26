import Mathlib

def sols : Finset (Fin 3 ↪ Set.Icc 1 5) := insert sorry sorry

/--
Generate the $3$-permutations of ${1,2,3,4,5}$.
-/
theorem brualdi_ch4_31 :
  Finset.univ (α := Fin 3 ↪ Set.Icc 1 5) = sols := by sorry
