import Mathlib

structure peaceful_rooks (n : ℕ) : Type where
  carrier :  Matrix (Fin n) (Fin n) Bool
  is_peaceful_row : ∀ i, List.count true (List.ofFn (fun j => carrier i j)) = 1
  is_peaceful_col : ∀ j, List.count true (List.ofFn (fun i => carrier i j)) = 1
deriving Fintype

noncomputable abbrev imo_2014_p2_solution (n : ℤ) (hn : n ≥ 2) : ℕ+ := sorry
/--
Let $n\ge2$ be an integer. Consider an $n\times n$ chessboard consisting of $n^2$ unit squares. A configuration of $n$ rooks on this board is $\textit{peaceful}$ if every row and every column contains exactly one rook. Find the greatest positive integer $k$ such that, for each peaceful configuration of $n$ rooks, there is a $k\times k$ square which does not contain a rook on any of its $k^2$ squares.
-/
theorem imo_2014_p2 (n : ℤ) (hn : n ≥ 2) :
  IsGreatest {(k : ℕ+) | ∀ r : peaceful_rooks n.toNat, ∃ i j : Fin n.toNat,
  i.val + k - 1 < n.toNat ∧ i.val + k - 1 < n.toNat ∧
  ∀ m n, m.val < k.1 ∧ n.val < k.1 ∧ r.carrier (i + m) (j + n) = false}
  (imo_2014_p2_solution n hn) := by sorry
