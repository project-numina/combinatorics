import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Sum

variable {α : Type}

namespace List

/--
For each element x of the list l returns it and the list of all elements
to the right of x, including x.
-/
def combinationsUnlimitedAux : List α → List (α × List α)
  | [] => []
  | x :: xs => (x, x :: xs) :: combinationsUnlimitedAux xs

/--
List of all r-combinations of the list l when arbitrary repeats
of the elements are allowed, as long as l doesn't contain duplicates.
-/
def combinationsUnlimited : ℕ → List α → List (List α)
  | 0, _ => [[]]
  | r + 1, l => List.flatten ((combinationsUnlimitedAux l).map (fun ⟨x, xs⟩ => (combinationsUnlimited r xs).map (List.cons x)))

end List

namespace Multiset

open List

def combinations (r : ℕ) (s : Multiset α) := Multiset.powersetCard r s

def combinationsUnlimitedAux (r : ℕ) (l : List α) : List (Multiset α) :=
  (combinationsUnlimited r l).map (↑)

theorem combinationsUnlimited_perm {r : ℕ} {l₁ l₂ : List α} (h : l₁ ~ l₂) :
  combinationsUnlimitedAux r l₁ ~ combinationsUnlimitedAux r l₂ := by sorry

def combinationsUnlimited (r : ℕ) (s : Multiset α) : Multiset (Multiset α) :=
  Quot.liftOn s (fun l => combinationsUnlimitedAux r l) (fun _ _ h => Quot.sound (combinationsUnlimited_perm h))

namespace Nodup

def combinationsUnlimited {r : ℕ} {s : Multiset α} (h : s.Nodup) :
  (combinationsUnlimited r s).Nodup := by sorry

end Nodup

end Multiset

namespace Finset

def combinationsUnlimited (r : ℕ) (s : Finset α) : Finset (Multiset α) :=
  ⟨s.1.combinationsUnlimited r, s.2.combinationsUnlimited⟩

/--
Theorem 2.5.1 Let S be a multiset with objects of k types, each with an
infinite repetition number. Then the number of r-combinations of S equals
$\binom{r + k - 1}{r} = \binom{r + k - 1}{k - 1}$.
-/
theorem combinationsUnlimited_card (r : ℕ) (s : Finset α) :
  (combinationsUnlimited r s).card = (r + s.card - 1).choose r := by sorry

end Finset
