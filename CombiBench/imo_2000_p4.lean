import Mathlib


-- 12

abbrev cards := Fin 100
abbrev boxs := Fin 3

abbrev allocation := { f : cards → boxs | Function.Surjective f }

-- the trick is that given the sum of any two cards, the magician can tell a box number
abbrev trick (f : allocation) :=
  ∀ (n : ℕ), (∃ c c' : cards, f.1 c ≠ f.1 c' ∧ n = c.1 + c'.1) → boxs

-- the trick works when:
def trick_works (f : allocation) (t : trick f) : Prop :=
  ∀ c₁ c₂ : cards,
  -- given the sum of two cards from box 0 and box 1 then the trick gives the result of box 2 **and**
  (∀ (h₁ : f.1 c₁ = 0) (h₂ : f.1 c₂ = 1),
    t (c₁.1 + c₂.1) ⟨c₁, c₂, by simp [*], rfl⟩ = 2) ∧
  -- given the sum of two cards from box 0 and box 2 then the trick gives the result of box 1 **and**
  (∀ (h₁ : f.1 c₁ = 0) (h₂ : f.1 c₂ = 2),
    t (c₁.1 + c₂.1) ⟨c₁, c₂, by simp [*], rfl⟩ = 1) ∧
  -- given the sum of two cards from box 1 and box 2 then the trick gives the result of box 0
  (∀ (h₁ : f.1 c₁ = 1) (h₂ : f.1 c₂ = 2),
    t (c₁.1 + c₂.1) ⟨c₁, c₂, by simp [*], rfl⟩ = 0)

def imo_2000_p4_sols : ℕ := sorry
/--
A magician has one hundred cards numbered $1$ to $100$. He puts them into three boxes, a red one, a white one and a blue one, so that each box contains at least one card. A member of the audience selects two of the three boxes, chooses one card from each and announces the sum of the numbers on the chosen cards. Given this sum, the magician identifies the box from which no card has been chosen. How many ways are there to put all the cards into the boxes so that this trick always works? (Two ways are considered different if at least one card is put into a different box.)
-/
theorem imo_2000_p4 (good_allocations : Finset allocation)
  (h : ∀ f ∈ good_allocations, ∃ (t : trick f), trick_works f t) :
  good_allocations.card = imo_2000_p4_sols := by sorry
