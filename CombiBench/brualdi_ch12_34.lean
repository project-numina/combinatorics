import Mathlib

variable (V : Type*) (G : SimpleGraph V)

/-- Prove that the complement of a disconnected graph is connected.-/
theorem brualdi_ch12_34 (h : ¬ G.Connected): Gᶜ.Connected := sorry
