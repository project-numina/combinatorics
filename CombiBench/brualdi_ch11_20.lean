import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Set.Card

variable (n : ℕ) (V : Type*) [Fintype V] (hV : Fintype.card V = n)
  (G : SimpleGraph V) (h : (n-1)*(n -2)/2 + 1 ≤ (SimpleGraph.edgeSet G).ncard)

/-- Prove that a graph of order n with at least `(n-1)(n-2)/2 + 1` edges must be connected.-/
theorem brualdi_ch11_20 : G.Connected := sorry
