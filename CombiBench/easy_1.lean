import Mathlib.Data.Fintype.Basic
import Combinatorics.PermutationsCombinations.Combinations

/--
How many ways can a teacher select a group of 6 students to sit in the front row if the class has 13 students?
-/
theorem easy_1 : (combinations 6 (@Finset.univ (Fin 13) _)).card = 1716 := by
  rw [← combinations_card]; rfl
