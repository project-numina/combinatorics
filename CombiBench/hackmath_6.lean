import Mathlib

noncomputable abbrev hackmath_6_solution_1 : ENNReal := sorry
noncomputable abbrev hackmath_6_solution_2 : ENNReal := sorry
noncomputable abbrev hackmath_6_solution_3 : ENNReal := sorry

/--
Two coins are tossed simultaneously. What is the probability of getting (i) At least one head? (ii) At most one tail? (iii) A head and a tail?
-/
theorem hackmath_6 : PMF.binomial (1/2 : _) ENNReal.half_le_self 2 1 +
    PMF.binomial (1/2 : _) ENNReal.half_le_self 2 2 = hackmath_6_solution_1 ∧
    PMF.binomial (1/2 : _) ENNReal.half_le_self 2 0 +
    PMF.binomial (1/2 : _) ENNReal.half_le_self 2 1 = hackmath_6_solution_2 ∧
    PMF.binomial (1/2 : _) ENNReal.half_le_self 2 1 = hackmath_6_solution_3 := by sorry
