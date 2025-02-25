import Mathlib

/--
Let $A$ be a matrix with $n$ columns, with integer entries taken from the set
$S=\{1,2, \ldots, k\}$. Assume that each integer $i$ in $S$ occurs exactly
$n r_{i}$ times in $A$, where $r_{i}$ is an integer.
Prove that it is possible to permute the entries in each row of $A$ to obtain
a matrix $B$ in which each integer $i$ in $S$ appears $r_{i}$ times in each column.
-/
theorem brualdi_ch9_13 (n m : ℕ) (k : ℕ+) (A : Matrix (Fin m) (Fin n) ℕ)
  (hA : ∀ i j, A i j ∈ Set.Icc 1 k.1) : ∃ (σ1 : Equiv.Perm (Fin n))
  (σ2 : Equiv.Perm (Fin m)), ∀ j : Fin m, ∀ x ∈ Set.Icc 1 k.1,
  List.count x ((List.finRange n).map ((A.submatrix σ2 σ1) j)) =
  ∑ x : Fin m, List.count i ((List.finRange n).map (A x) : List ℕ) := by sorry
