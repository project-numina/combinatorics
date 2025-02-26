import Mathlib

/-- Prove that a permutation and its inverse have the same type. -/
theorem brualdi_ch14_33 (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    σ.cycleType = σ⁻¹.cycleType := Equiv.Perm.cycleType_inv _ |>.symm
