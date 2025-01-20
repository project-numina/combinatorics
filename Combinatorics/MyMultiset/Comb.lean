import Combinatorics.MyMultiset.Basic

universe u

namespace MyMultiset

variable {α : Type u} (S : MyMultiset α)


structure Comb (n : ℕ) extends MyMultiset α where
  [rep_fin : toMyMultiset.RepIsFinite]
  [obj_fin : toMyMultiset.ObjIsFinite]
  rep_le (a : α) : toMyMultiset.rep a ≤ S.rep a
  card_eq : toMyMultiset.card = n

namespace Comb

attribute [instance] Comb.rep_fin Comb.obj_fin

variable {S}

@[ext]
lemma ext {n : ℕ} (a b : Comb S n) (h : a.toMyMultiset = b.toMyMultiset) : a = b := by
  cases a; cases b; simp only at h; subst h
  congr!
  exact Subsingleton.elim _ _

-- instance (n : ℕ) [DecidableEq α] : DecidableEq (S.Comb n) := by
--   intro a b
--   by_cases H : a.toMyMultiset = b.toMyMultiset
--   · refine .isTrue ?_
--     ext
--     simp [H]
--   · refine .isFalse ?_
--     rw [Comb.ext_iff]
--     exact H

def fromList' [DecidableEq α] (n : ℕ)
    (l : List α) (hl : l.length = n) (hl' : ∀ a, l.count a ≤ S.rep a) : S.Comb n :=
  let T : MyMultiset α :=
  { rep a := l.count a }
  letI : T.RepIsFinite :=
  { rep_finite a := by simp }
  letI : T.ObjIsFinite :=
  { support := List.toFinset l |>.filter fun a ↦ l.count a ≠ 0
    obj_finite a := by simp [List.count_eq_zero]
    dec a := by
      simp only [ne_eq, Finset.mem_filter, List.mem_toFinset]
      infer_instance }
  have hT : T.support = (List.toFinset l |>.filter fun a ↦ l.count a ≠ 0) := by
    ext; simp [List.count_eq_zero]
  have hT' (a : α) : T.repAsNat a = l.count a := by
    apply_fun ((↑) : ℕ → ℕ∞) using (Option.some_injective _)
    rw [repAsNat_spec]
  { T with
    rep_le := by simpa using hl'
    card_eq := by
      rw [card, hT]
      simp only [ne_eq, hT']
      rw [← hl]
      symm
      apply List.length_eq_sum_count' l }

def fromList [DecidableEq α] (n : ℕ) :
    {l : List α |  l.length = n ∧ ∀ a, l.count a ≤ S.rep a} → S.Comb n :=
  fun l ↦ fromList' n l.1 l.2.1 l.2.2

def fromFin  [DecidableEq α] (n : ℕ) :
    {v : Fin n → α | ∀ a, (List.ofFn v).count a ≤ S.rep a} → S.Comb n :=
  fun v ↦ fromList' n (List.ofFn v.1) (by simp) (by
    intro a
    simp only [Set.mem_setOf_eq]
    exact v.2 a)

@[simps]
def zero : S.Comb 0 where
  rep a := 0
  rep_fin :=
  { rep_finite := by simp }
  obj_fin :=
  { support := ∅
    obj_finite := by simp
    dec := by simp; infer_instance }
  rep_le a := by simp
  card_eq := by
    simp only [id_eq, eq_mpr_eq_cast]
    convert Finset.sum_empty

def finite_zero : Fintype (S.Comb 0) where
  elems := {zero}
  complete c := by
    simp only [Finset.mem_singleton]
    ext a
    simp only [zero_rep]
    by_cases h : a ∈ c.support
    · have : c.repAsNat a ≤ c.card := by
        rw [card]
        apply Finset.single_le_sum
        · simp
        · simpa using h
      rw [c.card_eq] at this
      simp only [nonpos_iff_eq_zero] at this
      apply_fun ((↑) : ℕ → ℕ∞) at this
      rw [repAsNat_spec] at this
      exact this
    simpa using h

instance (n : ℕ) : Fintype (S.Comb n) := sorry

end Comb


end MyMultiset
