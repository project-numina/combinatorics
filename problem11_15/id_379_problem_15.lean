import Mathlib

open Finset  Matrix

variable {m n k : ℕ}
variable (A : Matrix (Fin m) (Fin n) (Fin k))
variable (r : Fin k → ℕ)


def count_occurrences (f : Fin m → Fin k) (i : Fin k) : ℕ :=
  Fintype.card { x : Fin m // f x = i }

axiom A_occurrence_condition : ∀ i : Fin k,
  Fintype.card { p : Fin m × Fin n // A p.1 p.2 = i } = n * r i

/--
Let $A$ be a matrix with $n$ columns, with integer entries taken from the set $S={1,2, \ldots, k}$.
Assume that each integer $i$ in $S$ occurs exactly $n r_{i}$ times in $A$, where $r_{i}$ is an integer.
Prove that it is possible to permute the entries in each row of $A$ to obtain a matrix $B$ in which each
 integer $i$ in $S$ appears $r_{i}$ times in each column.
 -/
theorem exists_permutation_satisfying_B :
  ∃ (σ : Fin m → Fin m), Function.Bijective σ ∧
    (∀ j i, count_occurrences (fun x => A (σ x) j) i = r i) :=
sorry
  