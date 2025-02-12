import Mathlib.Probability.ProbabilityMassFunction.Binomial

/--
Two coins are tossed simultaneously. What is the probability of getting (i) At least one head? (ii) At most one tail? (iii) A head and a tail?
-/
theorem easy_6_1: PMF.binomial (1/2 : _) ENNReal.half_le_self 2 1 +
    PMF.binomial (1/2 : _) ENNReal.half_le_self 2 2 = 3/4 := by
  sorry

theorem easy_6_2: PMF.binomial (1/2 : _) ENNReal.half_le_self 2 0 +
    PMF.binomial (1/2 : _) ENNReal.half_le_self 2 1 = 3/4 := by
  sorry

theorem easy_6_3: PMF.binomial (1/2 : _) ENNReal.half_le_self 2 1 = 1/2 := by
  sorry
