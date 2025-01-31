/-
Evaluate the sum $\sum_{k=0}^{n}(-1)^{k}\binom{n}{k} 10^{k}$.
-/

import Mathlib.Data.Nat.Choose.Sum

namespace id_198_problem10

example : ∑ i in Finset.range (n + 1), (-1 : ℤ)^i * (n.choose i) * 10^i = (-9 : ℤ)^n := by
  sorry

end id_198_problem10
