import Mathlib

variable {α : Type*}

/-
Addition Principle: Suppose that a set S is partitioned into pairwise disjoint parts $S_1,S_2,
\ldots, S_m$. The number of objects in S can be determined by finding the number of objects in each
of the parts, and adding the numbers so obtained:  $|S| = |S_1| + |S_2| + \cdots + |S_m|$.
-/
-- This theorem has already been formalized in Mathlib under the name Finpartition.sum_card_parts.

/-
Multiplication Principle: Let S be a set of ordered pairs (a, b) of objects, where the first object
a comes from a set of size p, and for each choice of object a there are q choices for object b. Then
the size of S is p x q.
-/
-- This theorem has already been formalized in Mathlib under the name Multiset.card_product.

/--
Subtraction Principle: Let A be a set and let U be a larger set containing A. Let $\overline{A} = U
\setminus A = \{ x \in U : x \notin A \}$ be the complement of A in U. Then the number |A| of
objects in A is given by the rule: |A| = |U| - |$\overline{A}$|.
-/
theorem sub_card_sdiff {s t : Finset α} [DecidableEq α] (h : s ⊆ t) :
    s.card = t.card - (t \ s).card := by
  nth_rw 1 [← Finset.sdiff_union_of_subset h]
  rw [Finset.card_union_of_disjoint Finset.sdiff_disjoint]
  omega

/--
Division Principle. Let S be a finite set that is partitioned into k parts in such a way that each
part contains the same number of objects. Then the number of parts in the partition is given by the
rule: k = $\frac{|S|}{\text{number of objects in a part}}$.
-/
theorem card_parts_strict_eq_average [DecidableEq α] {s t: Finset α} {P : Finpartition s}
    (hP : ∀ a ∈ P.parts, ∀ b ∈ P.parts, a.card = b.card) (ht : t ∈ P.parts):
    P.parts.card = s.card / t.card := by
  specialize hP t ht
  have hs := Finpartition.sum_card_parts P
  by_cases ht' : t.card = 0
  · simp only [ht', Nat.div_zero, Finset.card_eq_zero, Finpartition.parts_eq_empty_iff,
    Finset.bot_eq_empty] at hP ⊢
    simp only [← Finset.card_eq_zero, ← hs, Finset.sum_eq_zero_iff]
    exact fun x a => Eq.symm ((fun {a b} => Nat.succ_inj'.mp) (congrArg Nat.succ (hP x a)))
  · symm
    rw [← hs, Nat.div_eq_iff_eq_mul_left (by omega)]
    · apply Finset.sum_eq_card_nsmul
      exact fun a a_1 => Eq.symm ((fun {a b} => Nat.succ_inj'.mp) (congrArg Nat.succ (hP a a_1)))
    · apply Finset.dvd_sum
      exact fun i a => dvd_of_eq (hP i a)
