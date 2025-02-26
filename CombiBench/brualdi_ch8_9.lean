import Mathlib

abbrev diff : (ℕ → ℤ) → (ℕ → ℤ) := fun a ↦ fun i ↦ a (i + 1) - a i

/-- Prove that the following formula holds for the k th-order differences of a sequence h0,h1,…,hn,… :[\Delta^{k} h_{n}=\sum_{j=0}^{k}(-1)^{k-j}\binom{k}{j} h_{n+j}]-/
theorem brualdi_ch8_9 (h : ℕ → ℤ) (k n : ℕ): (diff^k) h n = ∑ j : Fin (k + 1),
    (-1 : ℤ)^(k-j.1) * Nat.choose k j * h (n + j) := sorry
