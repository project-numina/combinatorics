import Mathlib.Probability.UniformOn

/-!
In this file we define picking the red marble being hitting the range 0 ≤ x < 10 in the
finite set of size 20. The probability in this case is induced by the counting measure
divided by 20.
-/
open MeasureTheory ProbabilityTheory ENNReal

/--
There are 10 red marbles, 6 green marbles, and 4 blue marbles in a box.
What is the probability of picking the next red marble?
-/
theorem easy_5 : uniformOn (Ω := (Fin 20)) ⊤ {i | i.1 < 10} = 1/2 := by
  erw [uniformOn_univ]
  rw [Measure.count_apply_finite' (Set.toFinite _) (by trivial), Set.Finite.card_toFinset,
    show Fintype.card (@Set.Elem (Fin 20) {(i : Fin 20) | i.1 < 10}) = 10 by rfl]
  simp only [Nat.cast_ofNat, Fintype.card_fin]
  rw [ENNReal.div_eq_div_iff] <;> simp; norm_num
