import Mathlib

structure Matrix.IsMagicSquare {n : ℕ} (m : Matrix (Fin n) (Fin n) ℕ) (s : ℕ) : Prop where
  distinct : m.uncurry.Injective
  elem_in i j : m i j ∈ Finset.Icc 1 (n^2)
  row_eq i : ∑ j, m i j = s
  col_eq i : ∑ j, m j i = s
  diag₁_eq : ∑ i, m i i = s
  diag₂_eq : ∑ i, m i i.rev = s

/-
Verify that there is no magic square of order 2.
-/
theorem brualdi_chi1_10 :
  ∀ (m : Matrix (Fin 2) (Fin 2) ℕ) (s : ℕ), ¬ m.IsMagicSquare s := sorry
