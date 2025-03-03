import Mathlib

/-- A difference set in a (Add)group with order n is a subset with order k such that
  for any -/
structure isDifferenceSet (n k : ℕ) (B : Finset (ZMod n)): Prop where
  size : B.card = k
  mem_appearance : ∀ x : (ZMod n), ∑ i ∈ B, ∑ j ∈ B\{i},
    List.count x [i - j] = (k * (k - 1))/(n - 1)

/--
Prove that $B={0,3,4,9,11}$ is a difference set in $Z_{21}$.
-/
theorem brualdi_ch10_31 : isDifferenceSet 21 5 {0, 3, 4, 9, 11} where
  size := sorry
  mem_appearance := sorry
