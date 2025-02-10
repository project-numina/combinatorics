import Mathlib.Data.Nat.Digits
import Combinatorics.missing.List

namespace Nat

@[simp]
lemma ofDigits_replicate_zero (b r : ℕ) :
    Nat.ofDigits b (List.replicate r 0) = 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    simp [List.replicate_succ, Nat.ofDigits_cons, ih]

@[simp]
lemma ofDigits_normalize (b : ℕ) (l : List ℕ) :
    Nat.ofDigits b (l.dropWhileRight (· = 0)) = Nat.ofDigits b l := by
  simp [← congr(ofDigits b $(l.dropWhileRight_eq_fillToLength 0)), List.fillToLength,
    ofDigits_append, ofDigits_replicate_zero]

lemma digits_ofDigits' (b : ℕ) (hb : 1 < b) (l : List ℕ) (hl : ∀ x ∈ l, x < b) :
    b.digits (ofDigits b l) = l.dropWhileRight (· = 0) := by
  rw [← ofDigits_normalize b l]
  rw [digits_ofDigits _ hb]
  · intro x hx
    exact hl _ <| l.dropWhileRight_sublist _ |>.mem hx
  · intro h
    simpa using l.dropWhileRight_getLast_not (· = 0) h

end Nat
