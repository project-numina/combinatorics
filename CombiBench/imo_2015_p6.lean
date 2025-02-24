import Mathlib

variable (a : ℕ+ → ℤ) (ha1 : ∀ j : ℕ+, 1 ≤ a j ∧ a j ≤ 2015)
  (ha2 : ∀ k l : ℕ+, k < l → k + a k ≠ l + a l)

/-- answer should b, N in the question.-/
def answer: Fin 2 → ℕ+ := ![sorry, sorry]

/--
The sequence $a_1,a_2,\dots$ of integers satisfies the conditions:
(i) $1\le a_j\le2015$ for all $j\ge1$,
(ii) $k+a_k\neq \ell+a_\ell$ for all $1\le k<\ell$.
Prove that there exist two positive integers $b$ and $N$
for which\[\left\vert\sum_{j=m+1}^n(a_j-b)\right\vert\le1007^2\]
for all integers $m$ and $n$ such that $n>m\ge N$.
-/
theorem imo_2015_p6 (n m : ℕ+) (hn : answer 1 < n) (hm : answer 2 < m) (h : m < n):
  |(∑ j ∈ Set.Icc (m + 1) n, (a j - answer 0))| ≤ 1007^2 := by sorry
