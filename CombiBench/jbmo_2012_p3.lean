import Mathlib

/--
On a board there are $n$ nails each two connected by a string. Each string is colored in one of $n$ given distinct colors. For each three distinct colors, there exist three nails connected with strings in these three colors. Can $n$ be\na) 6 ?\nb) 7 ?
-/
theorem jbmo_2012_p3 (n : ℕ) (G : SimpleGraph V) (e₁ e₂ e₃: Sym2 V) (he₁ : e₁∈ G.edgeSet) (he₁ : e₂ ∈ G.edgeSet)
(he₁ : e₃ ∈ G.edgeSet) (f : Sym2 (Finset (Fin n)) → Fin n ) :
 if ∃ e₁ e₂ e₃, f e₁ ≠ f e₂ ∧ f e₃ ≠ f e₂ ∧ f e₁ ≠ f e₃ ∧ e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ then True else False:= by sorry
