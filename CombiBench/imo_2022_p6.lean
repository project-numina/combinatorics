import Mathlib

structure NordicSquare (n : ℕ) where
  board : (Fin n × Fin n) → (Set.Icc 1 (n ^ 2))
  surj : Function.Surjective board

def adjacent {n : ℕ} (x y : Fin n × Fin n) : Prop :=
  (x.1.1 = y.1.1 ∧ x.2.1 = y.2.1 + 1) ∨ -- x and y are in the same column, x is one row above y
  (x.1.1 = y.1.1 ∧ y.2.1 = x.2.1 + 1) ∨ -- x and y are in the same column, x is one row below y
  (x.1.1 = y.1.1 + 1 ∧ x.2.1 = y.2.1) ∨ -- x and y are in the same row, x is one column to the left of y
  (y.1.1 = x.1.1 + 1 ∧ x.2.1 = y.2.1) -- x and y are in the same row, x is one column to the right of y

def valley {n : ℕ} (x : Fin n × Fin n) (sq : NordicSquare n) : Prop :=
  ∀ y : Fin n × Fin n, adjacent x y → sq.board x ≤ sq.board y

structure UphillPath {n : ℕ} (sq : NordicSquare n) where
  seq : RelSeries (α := Fin n × Fin n)
    (fun x y ↦ adjacent x y ∧ sq.board x < sq.board y)
  head : valley seq.head sq

instance {n : ℕ} (sq : NordicSquare n) : Finite (UphillPath sq) := by
  sorry

noncomputable instance {n : ℕ} (sq : NordicSquare n) : Fintype (UphillPath sq) := Fintype.ofFinite (UphillPath sq)

abbrev imo_2022_p6_solution : ℕ → ℕ := fun n => 2 * n ^ 2 - 2 * n + 1

/--
Let $n$ be a positive integer. A Nordic square is an $n \times n$ board containing all the integers from $1$ to $n^2$ so that each cell contains exactly one number. Two different cells are considered adjacent if they share an edge. Every cell that is adjacent only to cells containing larger numbers is called a valley. An uphill path is a sequence of one or more cells such that: (i) the first cell in the sequence is a valley, (ii) each subsequent cell in the sequence is adjacent to the previous cell, and (iii) the numbers written in the cells in the sequence are in increasing order. Find, as a function of $n$, the smallest possible total number of uphill paths in a Nordic square.
-/
lemma imo_2022_p6 (n : ℕ) (hn : n > 0) : IsLeast
  {k | ∃ (sq : NordicSquare n), k = Fintype.card (UphillPath sq)} (imo_2022_p6_solution n) := by
  sorry
