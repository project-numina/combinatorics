import Mathlib

variable (n s : ℕ)

@[ext]
structure isMagicSquare (n s : ℕ) (M : Matrix (Fin n) (Fin n) ℕ) : Prop where
  mem : ∀ i j, M i j ∈ Finset.Icc 1 (n * n)
  pairwise : ∀ i j i' j', i ≠ i' ∨ j ≠ j' → M i j ≠ M i' j'
  column_sum : ∀ i, ∑ j, M i j = s
  row_sum : ∀ j, ∑ i, M i j = s

abbrev replace : Matrix (Fin n) (Fin n) ℕ → Matrix (Fin n) (Fin n) ℕ :=
  fun A i j ↦ n^2 + 1 - A i j

/-- Show that the result of replacing every integer a in a magic square of order n
  with n^2 + 1 − a is a magic square of order n.-/
theorem brualdi_ch1_16 (M : Matrix (Fin n) (Fin n) ℕ) (hM : isMagicSquare n s M) :
  isMagicSquare n s (replace n M):= sorry
