import Mathlib

/-- Prove that the partition function satisfies pn > pn-1 when 2 ≤ n.-/
theorem brualdi_ch8_30 (n : ℕ) (hn : 2 ≤ n) :
  Fintype.card (Nat.Partition (n - 1)) < Fintype.card (Nat.Partition n) := sorry
