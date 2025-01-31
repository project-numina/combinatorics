/-
How many integers greater than 5400 have both of the following properties? (a) The digits are distinct. (b) The digits 2 and 7 do not occur.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Digits

namespace id_43_problem7

example (s : Finset ℕ)
    (hsa : ∀ n ∈ s, (Nat.digits 10 n).Nodup)
    (hsb : ∀ n ∈ s, 2 ∉ (Nat.digits 10 n) ∧ 7 ∉ (Nat.digits 10 n)) : s.card = 94830 := by sorry

end id_43_problem7
