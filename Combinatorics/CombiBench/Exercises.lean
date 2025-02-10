import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset
import Combinatorics.PermutationsCombinations.Permutations

open Finset

/--
1.1. How many four-digit even positive integers are there?
Answer: 4500
-/
theorem exercise_1_1 : ((Icc 1000 9999).filter Even).card = 4500 := by sorry

/--
1.2. How many onto functions f : {1, 2, 3, 4} → {a, b, c} are there?
Answer: 36
-/
theorem exercise_1_2 : ((@univ (Fin 4 → Fin 3)).filter Function.Surjective).card = 36 := by sorry

/--
1.3. Let S = {1, 2, …, 100}. If a three-element subset A = {a, b, c}
of S satisfies a + b = 3c, then A is said to have Property P.
Determine the number of three-element subsets of S that have Property P.
Answer: 1600

TODO: @roman make P decidable
-/
theorem exercise_1_3 :
    ((powersetCard 3 (Icc 1 100)).filter fun A ↦ ∃ a b c, A.card = 3 ∧ A = {a, b, c} ∧ a + b = 3 * c).card = 1600 := by sorry

-- TODO: @roman define matrix machinery in a separate library file --

def matrix (n : ℕ) := Fin n → Fin n → ℕ

def vector (n : ℕ) : List (Fin n) :=
  match n with
  | 0 => []
  | Nat.succ n' => go (Nat.succ n') n' (by linarith)
  where go (n i : ℕ) (h : i < n) : List (Fin n) :=
    match i with
    | 0 => [⟨0, h⟩]
    | Nat.succ i' => (go n i' (by linarith)) ++ [⟨Nat.succ i', h⟩]

def rows (X : matrix n) := List.map (fun i => X i) (vector n)

def columns (X : matrix n) := List.map (fun j i => X i j) (vector n)

def main_diagonal (X : matrix n) := fun i => X i i

def reverse (i : Fin n) : Fin n := ⟨n.pred - i, tsub_lt_of_lt (Nat.pred_lt_of_lt (Fin.pos i))⟩

def anti_diagonal (X : matrix n) := fun i => X i (reverse i)

def half (X : matrix n) := rows X ++ columns X ++ [main_diagonal X] ++ [anti_diagonal X]

def arrays (X : matrix n) := half X ++ List.map (fun f i => f (reverse i)) (half X)

/--
1.4. In a $5 \times 5$ matrix $X$, each element is either 0 or 1.
Let $x_{i, j}$ (where $i, j = 1, 2, \cdots, 5$) represent
the element in the $i$-th row and $j$-th column of $X$.
Consider all 24 five-element ordered arrays in the rows,
columns, and diagonals of $X$:
$$
\left(x_{i, 1}, x_{i, 2}, \cdots, x_{i, 5}\right),\left(x_{i, 5}, x_{i, 4}, \cdots, x_{i, 1}\right),
$$
where $i=1, 2, \cdots, 5$;
$$
\left(x_{1, j}, x_{2, j}, \cdots, x_{5, j}\right),\left(x_{5, j}, x_{4, j}, \cdots, x_{1, j}\right),
$$
where $j=1, 2, \cdots, 5$;
$$
\begin{array}{l}
\left(x_{1, 1}, x_{2, 2}, \cdots, x_{5, 5}\right),\left(x_{5, 5}, x_{4, 4}, \cdots, x_{1, 1}\right), \\
\left(x_{1, 5}, x_{2, 4}, \cdots, x_{5, 1}\right),\left(x_{5, 1}, x_{4, 2}, \cdots, x_{1, 5}\right).
\end{array}
$$

If all these arrays are pairwise distinct, find the possible values for the sum of all the elements in the matrix $X$.

Answer: 12 or 13
-/
theorem exercise_1_4
    (X : matrix 5) (hval : ∀ i j, X i j ≤ 1)
    (hnodup : List.Nodup (arrays X)) :
    ∑ i, ∑ j, X i j = 12 ∨ ∑ i, ∑ j, X i j = 13 := by sorry

/--
Source: https://rainymathboy.wordpress.com/wp-content/uploads/2011/01/102-combinatorial-problems.pdf - Advanced Problems 2
1.5. Let n be an odd integer greater than 1. Find the number of permutations
p of the set {1, 2, …, n} for which

|p(1) - 1| + |p(2) - 2| + … + |p(n) - n| = (n² - 1) / 2
-/
theorem exercise_1_5
    (n : ℕ) (hn : Odd n ∧ n > 1) :
    ((permutationsLength n (Icc 1 n)).filter (fun p ↦ (p.enum.map fun ⟨i, x⟩ ↦ |(x : ℤ) - (i.succ : ℤ)|).sum = ((n : ℤ) ^ 2 - 1) / 2)).card = n * ((n - 1) / 2).factorial^2 := by sorry
