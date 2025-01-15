import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Nat.Factorial.Basic

universe u

structure MyMultiset (α : Type u) where
  rep : α → Cardinal.{u}

namespace MyMultiset

class IsInfinite (S : MyMultiset α) : Prop where
  rep_infinite : ∀ (a : α), S.rep a >= ℵ₀

class IsFinite (S : MyMultiset α) : Prop where
  rep_finite : ∀ (a : α), S.rep a < ℵ₀

variable {α : Type*}  (S : MyMultiset α)

noncomputable def repAsNat [h : S.IsFinite] (a : α) : ℕ :=
  Cardinal.lt_aleph0.1 (h.rep_finite a) |>.choose

lemma repAsNat_spec [h : S.IsFinite] (a : α) : (S.repAsNat a : Cardinal) = S.rep a :=
  Cardinal.lt_aleph0.1 (h.rep_finite a) |>.choose_spec.symm

noncomputable def total [h : S.IsFinite] [Fintype α] : ℕ := ∑ a : α, S.repAsNat a

variable [DecidableEq α]
structure IsPerm (l : List α) (r : ℕ) : Prop where
  len : l.length = r                    -- the permutation has length `r`
  count (a : α) : l.count a ≤ S.rep a   -- the count of `a` in the permutation is at most `S.rep a`


def perm (r : ℕ) := { l : List α | S.IsPerm l r }

instance [Fintype α] : Fintype (S.perm r) := sorry

-- thm 2.4.1
theorem perm_count_of_infinity [Fintype α] [S.IsInfinite] :
    Fintype.card (S.perm r) = (Fintype.card α)^r := sorry


open scoped Nat
-- thm 2.4.2
example [Fintype α] [S.IsFinite] :
    Fintype.card (S.perm S.total) =
    (S.total !) / (∏ a : α, (S.repAsNat a) !) := sorry

end MyMultiset
