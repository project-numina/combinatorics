import Mathlib.Combinatorics.Derangements.Finite

/-
Prove that $D_{n}$ is an even number if and only if $n$ is an odd number.
-/

example (n : ℕ) : Even (numDerangements n) ↔ Odd n := by
  sorry
