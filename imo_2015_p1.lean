import Mathlib

variable (Point : Type) [MetricSpace Point]

def balanced (S : Set Point) : Prop :=
  ∀ (A B : Point), A ∈ S ∧ B ∈ S ∧ A ≠ B
  → ∃ C ∈ S, dist C A = dist C B

def centre_free (S : Set Point) : Prop :=
  ∀ (A B C : Point), A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ A ≠ B ∧ A ≠ C ∧ B ≠ C →
  ¬∃ P ∈ S, dist P A = dist P B ∧ dist P B = dist P C



/--
We say that a finite set $\mathcal{S}$ in the plane is balanced if, for any two different points $A$, $B$ in $\mathcal{S}$, there is a point $C$ in $\mathcal{S}$ such that $AC=BC$. We say that $\mathcal{S}$ is centre-free if for any three points $A$, $B$, $C$ in $\mathcal{S}$, there is no point $P$ in $\mathcal{S}$ such that $PA=PB=PC$. (1) Show that for all integers $n\geq 3$, there exists a balanced set consisting of $n$ points. (1) Determine all integers $n\geq 3$ for which there exists a balanced centre-free set consisting of $n$ points.
-/
theorem imo_2015_p1_1 (n : ℕ) (hn : 3 ≤ n):
  ∃ S : Set Point, Set.Finite S ∧ balanced Point S ↔ S.ncard = n := by
  sorry

/--
(2) n is odd
-/
theorem imo_2015_p1_2 (n : ℕ) (hn : 3 ≤ n):
  (∃ S : Set Point, Set.Finite S ∧ balanced Point S ∧ centre_free Point S ∧ S.ncard = n) ↔ Odd n := by
  sorry
