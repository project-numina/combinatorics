import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Card

namespace List

/--
For each element x of the list l returns it and the remaining part.
-/
def permutationsLengthAux : List α → List (α × List α)
  | [] => []
  | x :: xs => (x, xs) :: (permutationsLengthAux xs).map (fun ⟨y, ys⟩ => ⟨y, x :: ys⟩)

/--
List of all r-permutations of the list l
-/
def permutationsLength : ℕ → List α → List (List α)
  | 0, _ => [[]]
  | r + 1, l => List.flatten ((permutationsLengthAux l).map (fun ⟨x, xs⟩ => (permutationsLength r xs).map (List.cons x)))

end List

#eval List.permutationsLength 2 [1, 2, 3]

namespace Multiset

open List

theorem permutationsLength_perm {r : ℕ} {l₁ l₂ : List α} (h : l₁ ~ l₂) :
  permutationsLength r l₁ ~ permutationsLength r l₂ := by sorry

def permutationsLength (r : ℕ) (s : Multiset α) : Multiset (List α) :=
  Quot.liftOn s (fun l => List.permutationsLength r l) (fun _ _ h => Quot.sound (permutationsLength_perm h))

namespace Nodup

def permutationsLength {r : ℕ} {s : Multiset α} (h : s.Nodup) :
  (permutationsLength r s).Nodup := by sorry

end Nodup

end Multiset

namespace Finset

def permutationsLength (r : ℕ) (s : Finset α) : Finset (List α) :=
  ⟨s.1.permutationsLength r, s.2.permutationsLength⟩

/--
Theorem 2.2.1 For n and r positive integers with r ≤ s, P(n, r) = n × (n - 1) × … × (n - r + 1)
-/
theorem permutationsLength_card (r : ℕ) (s : Finset α) (h : r ≤ s.card) :
  (permutationsLength r s).card = s.card.factorial / (s.card - r).factorial := by sorry

end Finset
