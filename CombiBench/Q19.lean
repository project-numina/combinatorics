import Mathlib

/-!
Determine the domination number of the graph $Q_{3}$ of vertices and
edges of a three-dimensional cube.
-/

open SimpleGraph in
abbrev Q_3 := (pathGraph 2) □ (pathGraph 2) □ (pathGraph 2)

variable (n : ℕ)

abbrev dominatingNum (V : Type u) [Fintype V] (A : SimpleGraph V): ℕ := sorry

theorem Q19 : n = dominatingNum _ Q_3 := by sorry
