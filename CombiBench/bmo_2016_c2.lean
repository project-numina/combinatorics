import Mathlib

-- assume without loss of generality that the shop is open for 1 unit of time
-- `customer_enter_time` is the time at which each customer entered the shop
-- `customer_left_time` is the time at which each customer left the shop
def bmo_2016_c2_solution
    (customer_enter_time : Fin 2016 → Set.Icc 0 1)
    (customer_left_time : Fin 2016 → Set.Icc 0 1)
    (h : ∀ i, customer_enter_time i ≤ customer_left_time i) : ℕ := sorry

def solution_condition (customer_enter_time : Fin 2016 → Set.Icc 0 1)
    (customer_left_time : Fin 2016 → Set.Icc 0 1)
    (_ : ∀ i, customer_enter_time i ≤ customer_left_time i)
    (k : ℕ) : Prop :=
  ∃ (s : Fin k → Fin 2016),
    (∃ x ∈ Set.Icc 0 1, (∀ j, customer_enter_time (s j) ≤ x ∧ x ≤ customer_left_time (s j))) ∨
    (∀ i j : Fin k, i ≠ j → Set.Icc (customer_enter_time (s i)) (customer_left_time (s i)) ∩
      Set.Icc (customer_enter_time (s j)) (customer_left_time (s j)) = ∅)


/-- 50
There are 2016 customers who entered a shop on a particular day. Every customer entered the shop exactly once. (i.e. the customer entered the shop, stayed there for some time and then left the shop without returning back.)\nFind the maximal $k$ such that the following holds:\nThere are $k$ customers such that either all of them were in the shop at a specific time instance or no two of them were both in the shop at any time instance.
-/
theorem bmo_2016_c2
    (customer_enter_time : Fin 2016 → Set.Icc 0 1)
    (customer_left_time : Fin 2016 → Set.Icc 0 1)
    (h : ∀ i, customer_enter_time i ≤ customer_left_time i) :
    solution_condition customer_enter_time customer_left_time h
        (bmo_2016_c2_solution customer_enter_time customer_left_time h) ∧
    (∀ k, solution_condition customer_enter_time customer_left_time h k →
        k ≤ bmo_2016_c2_solution customer_enter_time customer_left_time h) := by sorry
