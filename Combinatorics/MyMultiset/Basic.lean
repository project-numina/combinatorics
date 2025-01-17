import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fin.VecNotation

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

class IsInfinite (S : MyMultiset α) : Prop where
  rep_infinite : ∀ (a : α), S.rep a = ⊤

class IsFinite (S : MyMultiset α) : Prop where
  rep_finite : ∀ (a : α), S.rep a ≠ ⊤

variable (S : MyMultiset α)

def repAsNat [h : S.IsFinite] (a : α) : ℕ :=
  S.rep a |>.untop (h.rep_finite a)

lemma repAsNat_spec [h : S.IsFinite] (a : α) : S.repAsNat a = S.rep a :=
  S.rep a |>.untop_eq_iff (h.rep_finite a) |>.1 rfl |>.symm

def total [h : S.IsFinite] [Fintype α] : ℕ := ∑ a : α, S.repAsNat a

instance (S : MyMultiset (Option α)) [h : S.IsFinite] : IsFinite (optionType S).1 := ⟨fun a ↦ by
  simpa using h.rep_finite _⟩

instance (S : MyMultiset (Option α)) [h : S.IsFinite] : IsFinite (optionType S).2 := ⟨fun a ↦ by
  simpa using h.rep_finite _⟩

instance (e : α ≃ β) [h : S.IsFinite] : IsFinite (S.equiv e) := ⟨fun a ↦ by
  simpa using h.rep_finite _⟩

instance (T : MyMultiset PEmpty) : IsFinite T := ⟨fun a ↦ by cases a⟩

@[simp]
lemma total_empty (T : MyMultiset PEmpty) : T.total = 0 := by
  simp only [total, Fintype.sum_empty]

@[simp]
lemma equiv_total [h : S.IsFinite] [Fintype α] [Fintype β] (e : α ≃ β) :
    (S.equiv e).total = S.total := by
  simp only [total, equiv_apply]
  apply Fintype.sum_bijective e.symm e.symm.bijective
  intro x
  simp only [repAsNat, comap_rep]

end MyMultiset
