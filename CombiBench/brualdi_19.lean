import Mathlib

open SimpleGraph in
abbrev Q_3 := (pathGraph 2) □ (pathGraph 2) □ (pathGraph 2)

variable (n : ℕ) {V : Type*} (G : SimpleGraph V)
open SimpleGraph BigOperators

def SimpleGraph.IsDominatingSet (D : Set V) : Prop :=
  ∀ v : V, ¬ (v ∈ D) →  ∃ u ∈ D, G.Adj u v

lemma IsDominatingSet.univ : G.IsDominatingSet Set.univ := by simp [IsDominatingSet]

noncomputable section
open scoped Classical in
def SimpleGraph.eDominationNum : ℕ∞ := iInf (fun s ↦ if
  (G.IsDominatingSet s) then s.card else ⊤ : (Finset V) → ℕ∞)

def SimpleGraph.dominationNum : ℕ := G.eDominationNum.toNat

/--
Determine the domination number of the graph $Q_{3}$ of vertices and
edges of a three-dimensional cube.
-/
theorem brualdi_19 : n = Q_3.dominationNum := by sorry

end
