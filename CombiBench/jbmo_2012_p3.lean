import Mathlib


abbrev jbmo_2012_p3_solution_a : Prop := sorry
abbrev jbmo_2012_p3_solution_b : Prop := sorry

/--
On a board there are $n$ nails each two connected by a string. Each string is colored in one of $n$ given distinct colors. For each three distinct colors, there exist three nails connected with strings in these three colors. Can $n$ be\na) 6 ?\nb) 7 ?
-/
theorem jbmo_2012_p3 (n : ℕ) (G : SimpleGraph V) (hG : G = completeGraph V) (color : Sym2 V → Fin n)
    (h : ∀ i j k : Fin n, ∃ v1 v2 v3 : V, s(v1, v2) ∈ G.edgeSet ∧ s(v2, v3) ∈ G.edgeSet ∧
    s(v3, v1) ∈ G.edgeSet ∧ color s(v1, v2) = i ∧ color s(v2, v3) = j ∧ color s(v3, v1) = k) :
    n = 6 := by sorry
