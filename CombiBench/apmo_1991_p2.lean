import Mathlib

namespace apmo_1991_p2

noncomputable def red_points (points : Fin k → ℝ × ℝ) : Finset (ℝ × ℝ) :=
  ((Finset.univ (α := Fin k × Fin k)).image (fun x => midpoint ℝ (points x.1) (points x.2)))
/-- 2
Suppose there are 997 points given in a plane. If every two points are joined by a line segment with its midpoint coloured in red, show that there are at least 1991 red points in the plane. Can you find a special case with exactly 1991 red points?
-/
theorem apmo_1991_p2 (points : Fin 997 → ℝ × ℝ) : (red_points points).card ≥ 1991 ∧
    (red_points (fun (i : Fin 997) => (0, 2 * (i + 1)))).card = 1991:= by
    sorry
