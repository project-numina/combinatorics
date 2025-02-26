import Mathlib

abbrev brualdi_ch6_9_solution : ℕ := sorry

open Finset in
/--Determine the number of integral solutions of the equation x1+x2+x3+x4=20 that satisfy 1≤x1≤6, 0≤x2≤7, 4≤x3≤8, 2≤x4≤6.-/
theorem brualdi_ch6_9 : {x : Fin 4 → ℕ | x0 ∈ Icc 1 6 ∧ x 1 ∈ Icc 0 7 ∧
  x 2 ∈ Icc 4 8 ∧ x 3 ∈ Icc 2 6}.ncard = brualdi_ch6_9_solution := by sorry
