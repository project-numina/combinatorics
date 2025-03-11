import Mathlib

abbrev board := Fin 3 × Fin 4

def formsDomino (i j : board) : Bool :=
  -- i and j are on the same row and (i is left to j or j is left to i)
  (i.1.val = j.1.val ∧ (i.2.val + 1 = j.2.val ∨ j.2.val + 1 = i.2.val)) ∨ -- or
  -- i and j are on the same column and (i is above j or j is above i)
  (i.2.val = j.2.val ∧ (i.1.val + 1 = j.1.val ∨ j.1.val + 1 = i.1.val))

structure PerfectCover where
  -- the collections of tiles
  d : Fin 6 → (board × board)
  -- each tile is a domino
  domino : ∀ i, formsDomino (d i).1 (d i).2
  -- every position on the board is covered by some dominos
  covers : ∀ i : board, ∃ j, i = (d j).1 ∨ i = (d j).2

noncomputable instance : Fintype PerfectCover :=
  Fintype.ofInjective PerfectCover.d <| by
    rintro ⟨d, _⟩ ⟨d', _⟩ (rfl : d = d')
    rfl

abbrev brualdi_ch1_5_solution : ℕ := sorry

/--
Find the number of different perfect covers of a 3-by-4 chessboard by dominoes.
-/
theorem brualdi_ch1_5 : Fintype.card PerfectCover = brualdi_ch1_5_solution := by sorry
