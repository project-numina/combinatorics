import Mathlib

/-
Let $n$ be a positive integer, and let $X_{n}$ be the set of $n$ ! permutations of ${1,2, \ldots, n}$.
Let $\pi$ and $\sigma$ be two permutations in $X_{n}$, and define $\pi \leq \sigma$ provided that the
set of inversions of $\pi$ is a subset of the set of inversions of $\sigma$. Verify that this defines
a partial order on $X_{n}$, called the inversion poset.
Describe the cover relation for this partial order and then draw the diagram for the inversion poset $\left(H_{4}, \leq\right)$.-/



variable {n: ℕ}


def inversion (σ: Equiv.Perm (Fin n)): Set (Fin n × Fin n) := { s | s.1 < s.2 ∧ σ s.1 > σ s.2 }

instance lt_by_inversion: LT (Equiv.Perm (Fin n)) := ⟨λ σ π => inversion σ ⊂ inversion π⟩
instance le_by_inversion: LE (Equiv.Perm (Fin n)) := ⟨λ σ π => inversion σ ⊆ inversion π⟩

instance inversion_po : PartialOrder (Equiv.Perm (Fin n)) where
  le_refl := by intro a; dsimp [LE.le]; simp
  le_trans := by
    intro a b c ha hb
    dsimp [LE.le] at *
    intro s hs
    exact hb <| ha hs
  le_antisymm := by
    -- this will be the non-trivial one
    intro a b ha hb
    have h' := Set.eq_of_subset_of_subset ha hb
    apply Equiv.Perm.ext
    contrapose! h'
    obtain ⟨x, hx⟩ :=  h'
    sorry

theorem id_181 {σ π: Equiv.Perm (Fin n)}: σ ⋖ π ↔
  (Nat.card (inversion σ) + 1 = Nat.card (inversion σ)):= by sorry
