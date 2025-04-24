import Mathlib

def inversion_number {n : ℕ} (j : Fin n) (σ : Equiv.Perm (Fin n)) : ℕ := sorry

def inversion_seq {n : ℕ} (σ : Equiv.Perm (Fin n)) : Fin n → ℕ := fun i ↦ inversion_number i σ
--   ∑ i : Fin n, if i < j ∧
#check Equiv.Perm.sign
#check Equiv.Perm.finPairsLT
#check Equiv.Perm.swapFactors

theorem inversion_unique {n : ℕ} (b : Fin n → ℕ) (hb : ∀ i : Fin n, b i ≤ n - 1 - i.1) :
  ∃! σ : Equiv.Perm (Fin n), inversion_seq σ = b := sorry
