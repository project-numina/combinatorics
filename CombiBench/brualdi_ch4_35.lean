import Mathlib

open List Lex

-- Define the complement
noncomputable def complement (n : ℕ) (a : List ℕ) : List ℕ := (List.Ico 1 (n+1)).filter (λ x => x ∉ a)

-- the r subset.
noncomputable def to_list_A (n r : ℕ) := ((((Finset.Ico 1 (n+1)).powersetCard r)).toList).map (Finset.toList)

-- the reverse order of (n-r) subset
noncomputable def to_list_B (n r : ℕ) :=  (((((Finset.Ico 1 (n+1)).powersetCard (n - r))).toList).map (Finset.toList)).reverse

/--
The complement $\bar{A}$ of an $r$-subset $A$ of $\{1,2, \ldots, n\}$ is the $(n-r)$-subset of $\{1,2, \ldots, n\}$,
consisting of all those elements that do not belong to $A$. Let $M=\binom{n}{r}$, the number of $r$-subsets and,
at the same time, the number of $(n-r)$ subsets of $\{1,2, \ldots, n\}$. Prove that, if $A_{1}, A_{2}, A_{3}, \ldots,
A_{M}$ are the $r$-subsets in lexicographic order, then $\overline{A_{M}}, \ldots, \overline{A_{3}}, \overline{A_{2}},
\overline{A_{1}}$ are the $(n-r)$-subsets in lexicographic order.
-/
theorem brualdi_ch4_35 (r n M : ℕ)  (hM : M = ((Finset.Ico 1 (n+1)).powersetCard r).card) :
 ∀ x y , x ∈ to_list_A n r ∧ y ∈ to_list_A  n r → Lex (· < ·) x y →
  complement n x ∈ to_list_B n r ∧ complement n y ∈ to_list_B n r →  Lex (· < ·) (complement n x) (complement n y) := by sorry
