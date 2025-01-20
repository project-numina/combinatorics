import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Combinatorics.missing.List
import Combinatorics.missing.Nat

open scoped Nat

set_option autoImplicit false

universe u

@[ext]
structure MyMultiset (α : Type u) where
  rep : α → ℕ∞

namespace MyMultiset

variable {α β : Type u}

@[simps]
def comap (f : α → β) (S : MyMultiset β) : MyMultiset α where
  rep := fun a ↦ S.rep (f a)

@[simps]
def equiv (e : α ≃ β) : MyMultiset α ≃ MyMultiset β where
  toFun := comap e.symm
  invFun := comap e
  left_inv := by intro S; ext a; simp [comap]
  right_inv := by intro S; ext b; simp [comap]

@[simps]
def sumType : MyMultiset (α ⊕ β) ≃ MyMultiset α × MyMultiset β where
  toFun S := ⟨⟨fun a ↦ S.rep (.inl a)⟩, ⟨fun b ↦ S.rep (.inr b)⟩⟩
  invFun S := ⟨Sum.rec (fun a ↦ S.1.rep a) (fun b ↦ S.2.rep b)⟩
  left_inv S := by
    ext a; rcases a with a|b  <;> simp
  right_inv S := rfl

@[simps!]
def optionType : MyMultiset (Option α) ≃ MyMultiset α × MyMultiset PUnit :=
  equiv (Equiv.optionEquivSumPUnit _) |>.trans sumType

abbrev original (S : MyMultiset (Option α)) : MyMultiset α := S.optionType.1

abbrev single (S : MyMultiset (Option α)) : MyMultiset PUnit := S.optionType.2

class IsInfinite (S : MyMultiset α) : Prop where
  rep_infinite : ∀ (a : α), S.rep a = ⊤

class RepIsFinite (S : MyMultiset α) : Prop where
  rep_finite : ∀ (a : α), S.rep a ≠ ⊤

class ObjIsFinite (S : MyMultiset α) where
  support : Finset α
  obj_finite : ∀ a, a ∈ support ↔ S.rep a ≠ 0
  dec : DecidablePred (fun a => a ∈ support)

variable (S : MyMultiset α)

def repAsNat [h : S.RepIsFinite] (a : α) : ℕ :=
  S.rep a |>.untop (h.rep_finite a)

attribute [instance] ObjIsFinite.dec

def support [h : S.ObjIsFinite] : Finset α := h.support

@[simp]
lemma mem_support [h : S.ObjIsFinite] (a : α) : a ∈ S.support ↔ S.rep a ≠ 0 := h.obj_finite a

lemma repAsNat_spec [h : S.RepIsFinite] (a : α) : S.repAsNat a = S.rep a :=
  S.rep a |>.untop_eq_iff (h.rep_finite a) |>.1 rfl |>.symm

def card [S.RepIsFinite] [S.ObjIsFinite] : ℕ := ∑ a ∈ S.support, S.repAsNat a

instance (S : MyMultiset (Option α)) [h : S.RepIsFinite] : RepIsFinite (optionType S).1 := ⟨fun a ↦ by
  simpa using h.rep_finite _⟩

instance (S : MyMultiset (Option α)) [h : S.RepIsFinite] : RepIsFinite (optionType S).2 := ⟨fun a ↦ by
  simpa using h.rep_finite _⟩

instance (e : α ≃ β) [h : S.RepIsFinite] : RepIsFinite (S.equiv e) := ⟨fun a ↦ by
  simpa using h.rep_finite _⟩

instance (e : α ≃ β) [h : S.ObjIsFinite] : ObjIsFinite (S.equiv e) where
  support := S.support.map e
  obj_finite a := by simp
  dec b := by
    rw [show b = e (e.symm b) by simp]
    simp only [Equiv.apply_symm_apply, Finset.mem_map_equiv, mem_support, ne_eq]
    infer_instance

@[simps]
def supportEquivEquiv (e : α ≃ β) [h : S.ObjIsFinite] : S.support ≃ (S.equiv e).support where
  toFun x := ⟨e x.1, by have := x.2; rw [mem_support] at this; simpa⟩
  invFun x := ⟨e.symm x.1, by have := x.2; rw [mem_support] at this; simpa⟩
  left_inv x := by simp
  right_inv x := by simp

instance (T : MyMultiset PEmpty) : RepIsFinite T := ⟨fun a ↦ by cases a⟩

instance (T : MyMultiset PEmpty) : ObjIsFinite T where
  support := ∅
  obj_finite a := a.elim
  dec := by infer_instance

@[simp]
lemma support_empty (T : MyMultiset PEmpty) : T.support = ∅ := by
  ext a
  simp only [mem_support, iff_false]
  cases a

@[simp]
lemma card_empty (T : MyMultiset PEmpty) : T.card = 0 := by
  simp only [card, support_empty, Finset.sum_empty]

instance [Fintype α] : S.ObjIsFinite where
  support := Finset.univ.filter (fun a => S.rep a ≠ 0)
  obj_finite a := by simp
  dec := by simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and]; infer_instance

instance : Subsingleton (S.ObjIsFinite) where
  allEq := by
    rintro ⟨S, hS, _⟩ ⟨T, hT, _⟩
    have : S = T := by
      ext a
      simp only [mem_support, hS, hT]
    subst this
    congr!

lemma fintype_support [Fintype α] : S.support = Finset.univ.filter (fun a => S.rep a ≠ 0) := by
  ext a
  simp only [mem_support, ne_eq, Finset.mem_filter, Finset.mem_univ, true_and]

lemma fintype_card [Fintype α] [S.ObjIsFinite] [S.RepIsFinite] :
    S.card = ∑ a : α, S.repAsNat a := by
  rw [card]
  rw [Finset.sum_subset]
  · exact Finset.subset_univ S.support
  rintro x -
  simp only [mem_support, ne_eq, Decidable.not_not]
  intro h
  apply_fun ((↑) : ℕ → ℕ∞) using (Option.some_injective _)
  rw [repAsNat_spec, h]
  rfl

instance [DecidableEq α] (S : MyMultiset (Option α)) [h : S.ObjIsFinite] :
    ObjIsFinite (S.optionType.1) where
  support := S.support \ {Option.none (α := α)} |>.attach.map
    { toFun := fun x ↦ Option.get x.1 (by
        have := x.2
        rw [Finset.mem_sdiff] at this
        rw [Option.isSome_iff_ne_none]
        simp only [mem_support, ne_eq, Finset.mem_singleton] at this
        exact this.2)
      inj' := by
        rintro ⟨⟨⟩|⟨x⟩, hx⟩ ⟨⟨⟩|⟨y⟩, hy⟩ h
        · aesop
        · aesop
        · aesop
        · simp only [Finset.mem_sdiff, mem_support, ne_eq, Finset.mem_singleton, reduceCtorEq,
          not_false_eq_true, and_true, Subtype.mk.injEq, Option.some.injEq] at hx hy ⊢
          exact h }
  obj_finite a := by
    simp only [Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk, true_and,
      Subtype.exists, Finset.mem_sdiff, mem_support, ne_eq, Finset.mem_singleton, optionType_apply]
    fconstructor
    · rintro ⟨a, ⟨⟨h, h'⟩, rfl⟩⟩
      simpa
    · intro h
      exact ⟨.some a, ⟨h, by simp⟩, rfl⟩
  dec := by
    intro a
    simp only [Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk, true_and,
      Subtype.exists, Finset.mem_sdiff, mem_support, ne_eq, Finset.mem_singleton]
    by_cases H : .some a ∈ S.support
    · exact .isTrue ⟨.some a, ⟨by simpa using H, by simp⟩, rfl⟩
    · refine .isFalse ?_
      simp only [not_exists]
      rintro (⟨⟩|⟨x⟩) h
      · simp at h
      · simp only [mem_support, ne_eq, Decidable.not_not] at H
        rintro rfl
        simp only [reduceCtorEq, not_false_eq_true, and_true, Option.get_some] at h H
        contradiction

@[simps]
def supportEquivOptionOriginalSupportOfNotMem [DecidableEq α]
    (S : MyMultiset (Option α)) [S.ObjIsFinite] (h : .none ∉ S.support) :
    S.support ≃
    S.original.support where
  toFun x := ⟨x.1.get (by
    rw [Option.isSome_iff_ne_none]
    intro hx
    have := x.2
    aesop), by
    have := x.2
    rw [mem_support] at this
    simpa [original]⟩
  invFun x := ⟨.some x.1, by
    have := x.2
    rw [mem_support] at this
    simpa⟩
  left_inv := by
    rintro ⟨⟨⟩|⟨x⟩, hx⟩
    · simp
    · simp
  right_inv := by
    rintro ⟨x, hx⟩
    simp

def supportEquivOptionOriginalSupportOfMem [DecidableEq α]
    (S : MyMultiset (Option α)) [S.ObjIsFinite] (h : .none ∈ S.support) :
  S.support ≃ Option (S.original.support) where
  toFun x := if h : x.1 = .none then .none else
    .some ⟨x.1.get (by rwa [Option.isSome_iff_ne_none]), by
      have := x.2
      rw [mem_support] at this
      simpa [original]⟩
  invFun := Option.rec ⟨.none, h⟩ fun a ↦ ⟨.some a.1, by
    have := a.2
    rw [mem_support] at this
    simpa⟩
  left_inv := by rintro ⟨⟨⟩|⟨x⟩, hx⟩ <;> simp
  right_inv := by rintro (⟨⟩|⟨x⟩) <;> simp

lemma original_card [DecidableEq α] (S : MyMultiset (Option α)) [h : S.RepIsFinite] [S.ObjIsFinite] :
    S.original.card = S.card - S.repAsNat .none := by
  by_cases H : .none ∈ S.support
  · simp only [card]
    conv_rhs => rw [← Finset.sum_attach]
    rw [Finset.sum_bijective (s := S.support.attach) (t := Finset.univ (α := Option _))
        (S.supportEquivOptionOriginalSupportOfMem H)
        (Equiv.bijective _) .., Fintype.sum_option]
    pick_goal 2
    · exact (fun x ↦ S.repAsNat x.1) ∘ (S.supportEquivOptionOriginalSupportOfMem H).symm
    pick_goal 2
    · rintro ⟨x, hx⟩; simp
    pick_goal 2
    · rintro ⟨x, hx⟩; simp
    simp only [supportEquivOptionOriginalSupportOfMem, Equiv.coe_fn_symm_mk, Function.comp_apply,
      Finset.univ_eq_attach, add_tsub_cancel_left]
    rw [← Finset.sum_attach]
    rfl
  · simp only [card]
    conv_rhs => rw [← Finset.sum_attach]
    rw [Finset.sum_bijective (s := S.support.attach) (t := Finset.univ (α := _))
        (S.supportEquivOptionOriginalSupportOfNotMem H)
        (Equiv.bijective _)]
    pick_goal 4
    · exact (fun x ↦ S.repAsNat x.1) ∘ (S.supportEquivOptionOriginalSupportOfNotMem H).symm
    pick_goal 2
    · rintro ⟨x, hx⟩; simp
    pick_goal 2
    · rintro ⟨x, hx⟩; simp
    simp only [mem_support, ne_eq, Decidable.not_not, Finset.univ_eq_attach, Function.comp_apply,
      supportEquivOptionOriginalSupportOfNotMem_symm_apply_coe] at H ⊢
    rw [show S.repAsNat none = 0 by
      apply_fun ((↑) : ℕ → ℕ∞) using (Option.some_injective _); rw [repAsNat_spec, H]; rfl]
    rw [← Finset.sum_attach]
    simp only [tsub_zero]
    rfl

@[simp]
lemma single_card (S : MyMultiset (Option α)) [S.RepIsFinite] :
    S.single.card = S.repAsNat .none := by
  rw [card]
  rw [Finset.sum_eq_single (a := ⟨⟩)]
  · rfl
  · rintro ⟨⟩ h h'
    simp only [ne_eq, not_true_eq_false] at h'
  · simp only [mem_support, ne_eq, Decidable.not_not]
    intro h
    apply_fun ((↑) : ℕ → ℕ∞) using (Option.some_injective _)
    rw [repAsNat_spec, h]
    rfl

lemma original_card' [DecidableEq α] (S : MyMultiset (Option α))
    [S.RepIsFinite] [S.ObjIsFinite] :
    S.original.card + S.single.card = S.card := by
  simp only [original_card, single_card]
  by_cases H : S.repAsNat .none = 0
  · rw [H]; simp
  rw [tsub_add_cancel_iff_le]
  rw [card]
  apply Finset.single_le_sum
  · simp only [mem_support, ne_eq, zero_le, implies_true]
  · simp only [mem_support, ne_eq]
    contrapose! H
    apply_fun ((↑) : ℕ → ℕ∞) using (Option.some_injective _)
    rw [repAsNat_spec, H]
    rfl

@[simp]
lemma original_repAsNat_eq
    (S : MyMultiset (Option α)) [h : S.RepIsFinite] (a : α) :
    (S.original.repAsNat a) = S.repAsNat (.some a) := by
  simp only [repAsNat, original, optionType_apply]

@[simp]
lemma equiv_card [S.RepIsFinite] [S.ObjIsFinite] (e : α ≃ β) :
    (S.equiv e).card = S.card := by
  rw [card, card, ← Finset.sum_attach]
  rw [Finset.sum_bijective (supportEquivEquiv S e).symm (t := Finset.univ)
    (he := Equiv.bijective _)]
  pick_goal 4
  · exact (fun x ↦ S.repAsNat (e.symm x.1)) ∘ (supportEquivEquiv S e)
  pick_goal 2
  · simp
  pick_goal 2
  · rintro ⟨b, hb⟩
    simp only [equiv_apply, comap, Finset.mem_attach, supportEquivEquiv, Equiv.coe_fn_mk,
      Equiv.coe_fn_symm_mk, Function.comp_apply, Equiv.apply_symm_apply, forall_const]
    rfl
  simp only [Finset.univ_eq_attach, equiv_apply, supportEquivEquiv, Equiv.coe_fn_mk,
    Function.comp_apply, Equiv.symm_apply_apply]
  symm
  rw [← Finset.sum_attach]

end MyMultiset
