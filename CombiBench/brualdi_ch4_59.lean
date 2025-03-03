import Mathlib

/-- 
Let $n \geq 2$ be an integer. Prove that the total number of inversions of all $n$ ! permutations of $1,2, \ldots, n$ equals $\frac{1}{2} n!\binom{n}{2}=n!\frac{n(n-1)}{4}$ (Hint: Pair up the permutations so that the number of inversions in each pair is $n(n-1) / 2$.)
-/
theorem brualdi_ch4_59 (n : ℕ) : ∑ σ : Equiv.Perm (Fin n),
    (Equiv.Perm.swapFactors (α := Fin n) σ).1.length =
    n! * n * (n-1) / 4 := sorry
