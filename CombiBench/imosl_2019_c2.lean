import Mathlib

set_option autoImplicit false

/-- 665
You are given a set of $n$ blocks, each weighing at least 1; their total weight is $2 n$. Prove that for every real number $r$ with $0 \\leqslant r \\leqslant 2 n-2$ you can choose a subset of the blocks whose total weight is at least $r$ but at most $r+2$.
-/

theorem imosl_2019_c2
    (n : ℕ)
    (blocks : Fin n → ℝ)
    (h1 : ∀ i, blocks i ≥ 1)
    (h2 : ∑ i, blocks i = 2 * n)
    (r : ℝ) (hr1 : 0 ≤ r) (hr2 : r ≤ 2*n - 2) :
    ∃ (s : Finset (Fin n)),
    (∑ i in s, blocks i) ≥ r ∧ (∑ i in s, blocks i) ≤ r + 2 := by sorry
