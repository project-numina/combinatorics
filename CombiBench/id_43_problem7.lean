import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Digits

/-
How many integers greater than 5400 have both of the following properties? (a) The digits are distinct. (b) The digits 2 and 7 do not occur.
-/

example (s : Finset ℕ)
    (hs2 : ∀ n ∈ s, n > 5400)
    (hs1 : ∀ n ∈ s, (Nat.digits 10 n).Nodup)
    (hs2 : ∀ n ∈ s, 2 ∉ (Nat.digits 10 n) ∧ 7 ∉ (Nat.digits 10 n)) : s.card = 94830 := by sorry
