import Combinatorics.PermutationsCombinations.Combinations
import Mathlib

open Nat Finset Set

variable {α : Type*} {n r : ℕ}

def A (n : ℕ) := Finset.Icc 1 n

-- Define the complement
def complement (n : ℕ) (a : Finset ℕ) : Finset ℕ :=
  (A n).filter (λ x => x ∉ a)

-- Convert to lexicographic order.
noncomputable def to_list_a' {n r : ℕ} := (Finset.toList (combinations r (A n))).reverse

-- Lexicographic order of the complement
noncomputable def to_list_b (n : ℕ) (a : Finset ℕ ) := (Finset.toList (complement n a)).reverse


/--
The complement $\bar{A}$ of an $r$-subset $A$ of $\{1,2, \ldots, n\}$ is the $(n-r)$-subset of $\{1,2, \ldots, n\}$,
consisting of all those elements that do not belong to $A$. Let $M=\binom{n}{r}$, the number of $r$-subsets and,
at the same time, the number of $(n-r)$ subsets of $\{1,2, \ldots, n\}$. Prove that, if $A_{1}, A_{2}, A_{3}, \ldots,
A_{M}$ are the $r$-subsets in lexicographic order, then $\overline{A_{M}}, \ldots, \overline{A_{3}}, \overline{A_{2}},
\overline{A_{1}}$ are the $(n-r)$-subsets in lexicographic order.
-/
theorem id_165 (r n M: ℕ) (A₀ : List (Finset ℕ ) ) (hA₀ : A₀.length = (combinations r (A n)).card) (hM : M = A₀.length ) :
  if A₀ = ((Finset.toList (combinations r (A n))).reverse)
  then  (A₀.map (complement n)).reverse =  (Finset.toList (combinations (n - r) (A n))).reverse  else False := by sorry
