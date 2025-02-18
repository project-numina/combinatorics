import Mathlib

/-- 373
Let $n$ be a positive integer. Dominoes are placed on a $2 n \\times 2 n$ board in such a way that every cell of the board is adjacent to exactly one cell covered by a domino. For each $n$, determine the largest number of dominoes that can be placed in this way. \n(A domino is a tile of size $2 \\times 1$ or $1 \\times 2$. Dominoes are placed on the board in such a way that each domino covers exactly two cells of the board, and dominoes do not overlap. Two cells are said to be adjacent if they are different and share a common side.)
-/
theorem egmo_2019_p2
  (n : ℕ) (hn : 0 < n) -- n 是正整数
  (sols : Finset ((Fin (2 * n) × Fin (2 * n)) × (Fin (2 * n) × Fin (2 * n))))
  (h_sols : ∀ d ∈ sols, (d.1.1.val < (2 * n - 1) → (d.1.2.val = d.2.2.val ∧ d.1.1.val + 1 = d.2.1.val)) ∨ (d.1.2.val < (2 * n - 1) → (d.1.1.val = d.2.1.val ∧ d.2.1.val + 1 = d.2.2.val)) -- 多米诺骨牌是两个连续的方块，为了避免重复，只考虑其中一个方向，限制 d.1 的坐标小于 d.2。 d.1 (x1, y1) → d.2 (x.1 + 1, y1) 或 d.1 (x1, y1) → d.2 (x1, y1 + 1)
   ∧ (∀ d₁ ∈ sols, ∀ d₂ ∈ sols, d₁.1 ≠ d₂.1 ∧ d₁.2 ≠ d₂.1 ∧ d₁.1 ≠ d₂.2 ∧ d₁.2 ≠ d₂.2)
   ∧ (∀ c : (Fin (2 * n) × Fin (2 * n)), (c ≠ d.1 ∧ c ≠ d.2) ∧ (
    ∃! d ∈ sols,
    (((d.1.1.val = c.1.val ∧ ((c.2.val < 2 * n - 1 → d.1.2.val = c.2.val + 1) ∨ (d.1.2.val < 2 * n - 1 → d.1.2.val + 1 = c.2.val))) ∨
    (d.1.2.val = c.2.val ∧ ((c.1.val < 2 * n - 1 → d.1.1.val = c.1.val + 1) ∨ (d.1.1.val < 2 * n - 1 → d.1.1.val + 1 = c.1.val)))) ∨
    ((d.2.1.val = c.1.val ∧ ((c.2.val < 2 * n - 1 → d.2.2.val = c.2.val + 1) ∨ (d.2.2.val < 2 * n - 1 → d.2.2.val + 1 = c.2.val))) ∨
    (d.2.2.val = c.2.val ∧ ((c.1.val < 2 * n - 1 → d.2.1.val = c.1.val + 1) ∨ (d.2.1.val < 2 * n - 1 → d.2.1.val + 1 = c.1.val)))))
   ))) :
  sols.card ≤ Nat.choose (n + 1) 2 := by
  sorry
