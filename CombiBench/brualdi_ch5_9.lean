import Mathlib

/--
Evaluate the sum $\sum_{k=0}^{n}(-1)^{k}\binom{n}{k} 10^{k}$.
-/
theorem brualdi_ch5_9 : ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (n.choose i) * 10 ^ i = (-9 : ℤ)^n := by sorry
