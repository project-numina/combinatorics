import Mathlib

/-- 942
There are given 100 distinct positive integers. We call a pair of integers among them good if the ratio of its elements is either 2 or 3. What is the maximum number $g$ of good pairs that these 100 numbers can form? (A same number can be used in several pairs.)
-/

structure goodPairs (s : Fin 100 ↪ ℕ+) where
    (i j : Fin 100)
    (ratio : s i = 2 * s j ∨ s i = 3 * s j)
deriving Fintype

theorem izho_2014_p3 :
    (∃ (s : Fin 100 ↪ ℕ+), Fintype.card (goodPairs s) = 180) ∧
    (∀ (s : Fin 100 ↪ ℕ+), Fintype.card (goodPairs s) ≤ 180) := by sorry
