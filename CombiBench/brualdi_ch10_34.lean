import Mathlib

structure SteinerTripleSystem (t k n : ℕ) (α : Type u) where
  carrier : Finset α
  card_eq_n : carrier.card = n
  blocks : Finset (Finset α)
  blocks_subset : ∀ b ∈ blocks, b ⊆ carrier
  card_blocks : blocks.card = k
  block_inner : ∀ s : (Finset α), s.card = t ∧ s ⊆ carrier →
    ∃! b ∈ blocks, s ⊆ b
/--
Let $t$ be a positive integer. Prove that, if there exists a Steiner triple system of index 1 having $v$ varieties, then there exists a Steiner triple system having $v^{t}$ varieties.
-/
theorem brualdi_ch10_34 (t : ℕ+) (v : ℕ): Nonempty (SteinerTripleSystem v 2 3 α) →
  Nonempty (SteinerTripleSystem (v^t.1) 2 3 α) := sorry
