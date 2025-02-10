import Mathlib

namespace brualdi_25
/--
Let the sequence $h_{0}, h_{1}, \ldots, h_{n}, \ldots$ be defined by $h_{n}=2 n^{2}-n+3,(n \geq 0)$. Find a formula for $\sum_{k=0}^{n} h_{k}$.
-/
theorem brualdi_25 (h : ℕ → ℝ) (h' : ∀ i, h i = 2 * i ^ 2 - i  + 3) :
    ∑ i ∈ Finset.range (n + 1), h i = (n + 1) * (4 * n ^ 2 - n + 18) / 6 := by
  sorry
