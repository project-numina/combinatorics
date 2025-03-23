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

instance {n : ℕ} (sq : NordicSquare n) : CoeFun (UphillPath sq)
    (fun x ↦ Fin (x.length + 1) → Fin n × Fin n) :=
  {coe f := f.1}

instance [NeZero n] (sq : NordicSquare n) : Inhabited (UphillPath sq) := sorry

lemma UphilPath_length_le {n : ℕ} (sq : NordicSquare n) (x : UphillPath sq) :
    x.length ≤ n ^ 2 := by
  by_contra! hn
  have hm : ∃ m1 m2 : Fin (x.length + 1), m1 < m2 ∧ x m1 = x m2 := by
    have hx : ¬ Function.Injective x := by
      by_contra hx
      have : Nat.card (Fin (x.length + 1)) ≤ Nat.card (Fin n × Fin n) := by
        exact Nat.card_le_card_of_injective x.toFun hx
      simp at this
      have : x.length ≤ n * n := by omega
      linarith!
    delta Function.Injective at hx
    push_neg at hx
    obtain ⟨m1, m2, h1, h2⟩ := hx
    if m1 < m2 then
      exact ⟨m1, m2, by assumption, h1⟩
    else
      exact ⟨m2, m1, by omega, h1.symm⟩
  obtain ⟨m1, m2, hm, hxxm⟩ := hm
  have hxxm' : sq.board (x m1) < sq.board (x m2) := by
    obtain ⟨m1, h1⟩ := m1
    obtain ⟨m2, h2⟩ := m2
    rw [Fin.mk_lt_mk] at hm
    have hm' := le_of_lt hm
    induction m2, hm' using Nat.le_induction with
    | base => simp at hm
    | succ n' hmn hh =>
      obtain ⟨hn1', hn2'⟩ := x.1.3 ⟨n', by omega⟩
      simp [adjacent] at hn1'
      cases hn1' with
      | inl h =>
        sorry
      | inr h => sorry

  exact (ne_of_lt hxxm') (congr_arg _ hxxm)

#exit
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
-- f : UphillPath sq → Finset (Fin n × Fin n)
-- f : a ↦ a.range?????
noncomputable instance {n : ℕ} (sq : NordicSquare n) : Fintype (UphillPath sq) :=
  .ofInjective (β := Set (Fin n × Fin n)) (fun f ↦ Set.range f.toFun) <| fun x y h ↦ by
    simp at h
    have hx : Finset.card (Set.range x.toFun) = x.length + 1 := by
      sorry
    have hl : x.length = y.length := by

      sorry

    sorry

abbrev imo_2022_p6_solution : ℕ → ℕ := sorry

/--
Let $n$ be a positive integer. A Nordic square is an $n \times n$ board containing all the integers from $1$ to $n^2$ so that each cell contains exactly one number. Two different cells are considered adjacent if they share an edge. Every cell that is adjacent only to cells containing larger numbers is called a valley. An uphill path is a sequence of one or more cells such that: (i) the first cell in the sequence is a valley, (ii) each subsequent cell in the sequence is adjacent to the previous cell, and (iii) the numbers written in the cells in the sequence are in increasing order. Find, as a function of $n$, the smallest possible total number of uphill paths in a Nordic square.
-/
lemma imo_2022_p6 (n : ℕ) (hn : n > 0) : IsLeast
  {k | ∃ (sq : NordicSquare n), k = Fintype.card (UphillPath sq)} (imo_2022_p6_solution n) := by
  sorry
