import Mathlib


namespace PebbleGame

open Finset


structure Pebble (n : ℕ) where
  weight : ℕ
  color : Fin n
deriving Repr

instance {n : ℕ} : DecidableEq (Pebble n) :=
  fun x y =>
    if h : x.weight = y.weight ∧ x.color = y.color then
      isTrue (by cases x; cases y; simp at h; simp [h])
    else
      isFalse (by intro H; cases x; cases y; simp at H; exact h H)

def PebbleSet (n : ℕ) (h : 0 < n): Multiset (Pebble n) :=
  (Multiset.range (4 * n)).map (λ i => ⟨i + 1, ⟨i % n, Nat.mod_lt i h⟩⟩)


def ValidSplit (n : ℕ) (S : Finset (Pebble n)) (h : 0 < n) : Prop :=
  let T := (PebbleSet n h).toFinset \ S
  (S.sum Pebble.weight = T.sum Pebble.weight) ∧
  (∀ c : Fin n, (S.filter (λ p => p.color = c)).card = 2)

/-- 708
There are $4n$ pebbles of weights $1, 2, 3, \ldots, 4n$. Each pebble is colored in one of $n$ colors and there are four pebbles
of each color. Show that we can arrange the pebbles into two piles so that the following two conditions are both satisfied:
 1) The total weights of both piles are the same.
 2) Each pile contains two pebbles of each color.
-/
theorem imo_2020_p3 (n : ℕ) (h : 0 < n) :
  ∃ S : Finset (Pebble n), ValidSplit n S h:=
  by
  sorry

end PebbleGame
