import Combinatorics.MyMultiset.Basic
import Mathlib.Data.Sym.Card

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

lemma repAsNat_le {n : ℕ} (c : Comb S n) (a : α) : c.repAsNat a ≤ S.rep a := by
  rw [c.repAsNat_spec]
  exact c.rep_le a

lemma repAsNat_le_length {n : ℕ} (c : Comb S n) (a : α) : c.repAsNat a ≤ n := by
  by_cases h : a ∈ c.support
  · simp_rw [← c.card_eq]
    apply Finset.single_le_sum
    · aesop
    · assumption
  simp only [mem_support, ne_eq, Decidable.not_not] at h
  rw [show c.repAsNat a = 0 by
    apply_fun ((↑) : ℕ → ℕ∞) using Option.some_injective _; rw [repAsNat_spec]; simp [h]]
  aesop

lemma rep_le_length {n : ℕ} (c : Comb S n) (a : α) : c.rep a ≤ n := by
  rw [← c.repAsNat_spec]
  simp only [Nat.cast_le]
  exact c.repAsNat_le_length a

variable (S) in
@[simps]
def equivIntegerSolutions [fin : S.ObjIsFinite] [DecidableEq α] (n : ℕ) :
    S.Comb n ≃
    (v : S.support → Fin (n + 1)) ×'
    ((∀ a : S.support, (v a).1 ≤ S.rep a.1) ∧ ∑ i : S.support, (v i).1 = n) where
  toFun c := ⟨fun a ↦ ⟨c.repAsNat a, by have := c.repAsNat_le_length a; omega⟩, by
    intro a
    simp only
    exact c.repAsNat_le a, by
    dsimp
    conv_rhs => rw [← c.card_eq, card]
    symm
    rw [← Finset.sum_attach]
    fapply Finset.sum_of_injOn
    · exact fun i => ⟨i.1, by
        simp only [mem_support, ne_eq]
        intro rid
        have := c.rep_le i.1
        simp only [rid, nonpos_iff_eq_zero] at this
        have := i.2
        rw [mem_support] at this
        contradiction⟩
    · rintro ⟨x, hx⟩ - ⟨y, hy⟩ -
      simp only [Subtype.mk.injEq, imp_self]
    · rintro ⟨i, hi⟩ h
      simp only [Finset.mem_coe, Finset.mem_attach]
    · rintro ⟨i, hi⟩ h
      simp only [Set.mem_image, Finset.mem_coe, Finset.mem_attach, Subtype.mk.injEq, true_and,
        Subtype.exists, mem_support, ne_eq, exists_prop, exists_eq_right, Decidable.not_not,
        repAsNat]
      aesop
    · aesop⟩
  invFun p :=
    { rep a := if h : a ∈ S.support then p.1 ⟨a, h⟩ else 0
      rep_fin := ⟨fun a ↦ by aesop⟩
      obj_fin :=
        { support := (S.support.attach.filter fun a ↦ p.1 a ≠ 0).image Subtype.val
          obj_finite a := by
            simp only [Finset.univ_eq_attach, ne_eq, Finset.mem_image, Finset.mem_filter,
              Finset.mem_attach, true_and, Subtype.exists, mem_support, exists_and_right,
              exists_eq_right, dite_not, dite_eq_left_iff, Nat.cast_eq_zero, not_forall]
            rw [exists_congr]
            intro h
            refine ⟨?_, by aesop⟩
            contrapose!
            intro h
            ext
            exact h
          dec := by
            simp only [Finset.univ_eq_attach, ne_eq, Finset.mem_image, Finset.mem_filter,
              Finset.mem_attach, true_and, Subtype.exists, mem_support, exists_and_right,
              exists_eq_right]
            infer_instance }
      rep_le a := by
        simp only [mem_support, ne_eq, Finset.univ_eq_attach, dite_not]
        split_ifs with h
        · aesop
        · exact p.2.1 ⟨a, _⟩
      card_eq := by
        simp only [card, mem_support, ne_eq, Finset.univ_eq_attach, eq_mpr_eq_cast, dite_not, ←
          p.2.2]
        rw [← Finset.sum_attach]
        fapply Finset.sum_of_injOn
        · exact fun i => ⟨i.1, by
            simp only [mem_support, ne_eq, Finset.univ_eq_attach, id_eq, eq_mpr_eq_cast,
              Fin.val_zero, eq_mp_eq_cast]
            intro rid
            have := i.2
            rw [mem_support] at this
            simp only [mem_support, ne_eq, Finset.univ_eq_attach, id_eq, eq_mpr_eq_cast,
              Fin.val_zero, eq_mp_eq_cast, dite_not, dite_eq_left_iff, Nat.cast_eq_zero,
              not_forall] at this
            obtain ⟨h, -⟩ := this
            contradiction⟩
        · rintro ⟨x, hx⟩ - ⟨y, hy⟩ -
          simp
        · rintro ⟨i, hi⟩ h; simp
        · rintro ⟨i, hi⟩ - h
          simp only [mem_support, ne_eq, Finset.univ_eq_attach, id_eq, eq_mpr_eq_cast, Fin.val_zero,
            eq_mp_eq_cast, Set.mem_image, Finset.mem_coe, Finset.mem_attach, Subtype.mk.injEq,
            true_and, Subtype.exists, dite_not, dite_eq_left_iff, Nat.cast_eq_zero, not_forall,
            exists_prop, exists_eq_right, not_exists, Decidable.not_not] at h
          apply h
          simpa using hi
        · rintro ⟨x, hx⟩ -
          simp only [mem_support, ne_eq, dite_not, dite_eq_left_iff, Nat.cast_eq_zero,
            not_forall] at hx ⊢
          obtain ⟨h1, h2⟩ := hx
          simp only [repAsNat, dif_neg h1]
          rfl }
  left_inv := by
    rintro x
    ext a
    simp only [mem_support, ne_eq, dite_eq_ite, ite_not]
    split_ifs with h
    · have := x.rep_le a
      rw [h] at this
      simp only [nonpos_iff_eq_zero] at this
      exact this.symm
    · rw [repAsNat_spec]
  right_inv := by
    rintro ⟨v, h1, h2⟩
    ext a
    · simp only [mem_support, ne_eq, dite_not]
      apply_fun ((↑) : ℕ → ℕ∞) using Option.some_injective _
      simp only [repAsNat_spec, Subtype.coe_eta, dite_eq_ite, ite_eq_right_iff]
      intro h
      specialize h1 a
      rw [h] at h1
      simp only [nonpos_iff_eq_zero, Nat.cast_eq_zero] at h1
      simp [h1]
    · exact proof_irrel_heq _ _

instance {n : ℕ} [fin : S.ObjIsFinite] [DecidableEq α] : Fintype (S.Comb n) :=
  Fintype.ofEquiv _ (equivIntegerSolutions (n := n) (S := S)).symm

variable (S) in
@[simps!]
def equivIntegerSolutionsOfIsInfinite
    (n : ℕ) [fin : S.ObjIsFinite] [inf : S.IsTotallyInfinite] [DecidableEq α] :
    S.Comb n ≃ (v : S.support → Fin (n + 1)) ×' (∑ i : S.support, (v i).1 = n) :=
  equivIntegerSolutions S n |>.trans
  { toFun v := ⟨v.1, v.2.2⟩
    invFun v := ⟨v.1, ⟨by intros; simp [inf.rep_infinite], v.2⟩⟩
    left_inv := by rintro ⟨v, h⟩; simp
    right_inv := by rintro ⟨v, h⟩; simp }

variable (S) in
@[simps!]
def equivIntegerSolutionsOfIsInfiniteOfFintype
    (n : ℕ) [Fintype α] [inf : S.IsTotallyInfinite] [DecidableEq α] :
    S.Comb n ≃ (v : α → Fin (n + 1)) ×' (∑ i : α, (v i).1 = n) :=
  equivIntegerSolutionsOfIsInfinite S n |>.trans
  { toFun v := ⟨fun a ↦ if h : a ∈ S.support then v.1 ⟨a, h⟩ else 0, by
      simp only [mem_support, ne_eq, Finset.univ_eq_attach, dite_not]
      simp_rw [← v.2]
      symm
      fapply Finset.sum_of_injOn
      · exact Subtype.val
      · exact Set.injOn_subtype_val
      · intro; aesop
      · intro; aesop
      · rintro ⟨x, hx⟩ -
        simp only [Finset.univ_eq_attach]
        rw [dif_neg (by simpa using hx)]⟩
    invFun v := ⟨v.1 ∘ Subtype.val, by
      simp_rw [← v.2]
      fapply Finset.sum_of_injOn
      · exact Subtype.val
      · exact Set.injOn_subtype_val
      · intro; aesop
      · rintro x - h
        simp only [Finset.univ_eq_attach, Set.mem_image, Finset.mem_coe, Finset.mem_attach,
          true_and, Subtype.exists, mem_support, ne_eq, exists_prop, exists_eq_right,
          Decidable.not_not] at h
        have := inf.rep_infinite x
        simp [h] at this
      · rintro ⟨x, hx⟩ -
        simp⟩
    left_inv := by
      rintro ⟨v, h⟩
      ext ⟨x, hx⟩
      · simp only [mem_support, ne_eq, dite_not, Function.comp_apply]
        rw [dif_neg (by simpa using hx)]
      · exact proof_irrel_heq _ _
    right_inv := by
      rintro ⟨v, h⟩
      ext x
      · simp only [mem_support, ne_eq, Function.comp_apply, dite_eq_ite, ite_not]
        split_ifs with h
        · have := inf.rep_infinite x
          simp [h] at this
        · rfl
      · exact proof_irrel_heq _ _ }

variable (S) in
@[simps!]
def equivSymOfIsInfiniteOfFintype
    (n : ℕ) [Fintype α] [inf : S.IsTotallyInfinite] [DecidableEq α] :
    S.Comb n ≃ Sym α n :=
  equivIntegerSolutionsOfIsInfiniteOfFintype S n |>.trans
  { toFun v := ⟨∑ a : α, (v.1 a).1 • {a}, by simp [v.2]⟩
    invFun v := ⟨fun a ↦ ⟨v.1.count a, by
      have := Multiset.count_le_card a v.1
      rw [v.2] at this
      omega⟩, by simp⟩
    left_inv := by
      rintro ⟨v, h⟩
      ext a
      · simp [Multiset.count_sum', Multiset.count_singleton]
      · exact proof_irrel_heq _ _
    right_inv := by
      rintro v
      ext a
      simp [Multiset.count_sum', Multiset.count_singleton] }

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

instance finite_zero : Fintype (S.Comb 0) where
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

-- theorem 2.5.1
theorem card_of_isInfinite_ofFintype [Fintype α] [DecidableEq α] [S.IsTotallyInfinite] (n : ℕ) :
    Fintype.card (S.Comb n) = (Fintype.card α + n - 1).choose n := by
  rw [← Sym.card_sym_eq_choose (α := α) n]
  apply Fintype.card_congr
  exact equivSymOfIsInfiniteOfFintype S n

end Comb

end MyMultiset
