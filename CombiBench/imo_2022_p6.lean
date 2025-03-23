import Mathlib

structure NordicSquare (n : ℕ) where
  board : (Fin n × Fin n) → (Finset.Icc 1 (n ^ 2))
  bij : Function.Bijective board

def adjacent {n : ℕ} (x y : Fin n × Fin n) : Prop :=
  (x.1.1 = y.1.1 ∧ x.2.1 = y.2.1 + 1) ∨ -- x and y are in the same column, x is one row above y
  (x.1.1 = y.1.1 ∧ y.2.1 = x.2.1 + 1) ∨ -- x and y are in the same column, x is one row below y
  (x.1.1 = y.1.1 + 1 ∧ x.2.1 = y.2.1) ∨ -- x and y are in the same row, x is one column to the left of y
  (y.1.1 = x.1.1 + 1 ∧ x.2.1 = y.2.1) -- x and y are in the same row, x is one column to the right of y

def valley {n : ℕ} (x : Fin n × Fin n) (sq : NordicSquare n) : Prop :=
  ∀ y : Fin n × Fin n, adjacent x y → sq.board x ≤ sq.board y

structure UphillPath {n : ℕ} (sq : NordicSquare n) extends RelSeries (α := Fin n × Fin n)
    (fun x y ↦ adjacent x y ∧ sq.board x < sq.board y) where
  head : valley toRelSeries.head sq

instance [NeZero n] (sq : NordicSquare n) : Inhabited (UphillPath sq) := sorry

-- lemma

instance {n : ℕ} (sq : NordicSquare n) : Finite (UphillPath sq) := by sorry
  -- classical
  -- if h : n = 0 then
  -- have : IsEmpty (UphillPath sq) := {
  --   false x := by
  --     have := x.1
  --     subst h
  --     simp at this
  --     haveI : IsEmpty (Fin 0 × Fin 0) := by exact Prod.isEmpty_right
  --     haveI : IsEmpty (RelSeries (fun x y ↦ adjacent x y ∧ sq.board x < sq.board y)) := inferInstance
  --     exact IsEmpty.false (α := (RelSeries (fun x y ↦ adjacent x y ∧ sq.board x < sq.board y))) x.1
  -- }
  -- exact Finite.of_subsingleton
  -- else
  -- haveI : NeZero n := ⟨h⟩
  -- exact Finite.of_surjective (α := RelSeries (fun x y ↦ adjacent x y ∧ sq.board x < sq.board y))
  --   (fun x ↦ if h : valley x.head sq then ⟨x, h⟩ else default) <| fun x ↦ ⟨x.1, by simp [x.2]⟩

noncomputable instance {n : ℕ} (sq : NordicSquare n) : Fintype (UphillPath sq) := Fintype.ofFinite (UphillPath sq)

abbrev imo_2022_p6_solution : ℕ → ℕ := sorry

/--
Let $n$ be a positive integer. A Nordic square is an $n \times n$ board containing all the integers from $1$ to $n^2$ so that each cell contains exactly one number. Two different cells are considered adjacent if they share an edge. Every cell that is adjacent only to cells containing larger numbers is called a valley. An uphill path is a sequence of one or more cells such that: (i) the first cell in the sequence is a valley, (ii) each subsequent cell in the sequence is adjacent to the previous cell, and (iii) the numbers written in the cells in the sequence are in increasing order. Find, as a function of $n$, the smallest possible total number of uphill paths in a Nordic square.
-/
lemma imo_2022_p6 (n : ℕ) (hn : n > 0) : IsLeast
  {k | ∃ (sq : NordicSquare n), k = Fintype.card (UphillPath sq)} (imo_2022_p6_solution n) := by
  sorry
