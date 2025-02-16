import Mathlib

-- note that writing `n` as sum of elements of `S` will have at most n terms.
def clean (S : Set ℕ+) (n : ℕ) : Prop :=
  ∃! (f : Fin n →₀ ℕ),
    (∑ i ∈ f.support, f i = n) ∧
    (Odd f.support.card) ∧
    (∀ (i : Fin n) (h : i ∈ f.support), ⟨f i, Nat.pos_of_ne_zero <| by aesop⟩ ∈ S)

/-- 594
Let $S$ be a nonempty set of positive integers. We say that a positive integer $n$ is clean if it has a unique representation as a sum of an odd number of distinct elements from $S$. Prove that there exist infinitely many positive integers that are not clean.
-/
theorem imosl_2015_c6 (S : Set ℕ+) : ∀ (N : ℕ), ∃ (m : ℕ), N < m ∧ ¬ clean S m := by sorry
