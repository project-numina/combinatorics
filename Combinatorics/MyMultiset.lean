import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Nat.Factorial.Basic

set_option autoImplicit false

open scoped Cardinal

universe u

structure MyMultiset (α : Type u) where
  rep : α → Cardinal.{u}

namespace MyMultiset

variable {α β : Type u}

def comap (f : α → β) (S : MyMultiset β) : MyMultiset α :=
  { rep := fun a ↦ S.rep (f a) }

class IsInfinite (S : MyMultiset α) : Prop where
  rep_infinite : ∀ (a : α), S.rep a >= ℵ₀

class IsFinite (S : MyMultiset α) : Prop where
  rep_finite : ∀ (a : α), S.rep a < ℵ₀

variable (S : MyMultiset α)

noncomputable def repAsNat [h : S.IsFinite] (a : α) : ℕ :=
  Cardinal.lt_aleph0.1 (h.rep_finite a) |>.choose

lemma repAsNat_spec [h : S.IsFinite] (a : α) : (S.repAsNat a : Cardinal) = S.rep a :=
  Cardinal.lt_aleph0.1 (h.rep_finite a) |>.choose_spec.symm

noncomputable def total [h : S.IsFinite] [Fintype α] : ℕ := ∑ a : α, S.repAsNat a

variable [DecidableEq α]

structure Perm (r : ℕ) where
  ℓ : List α
  len : ℓ.length = r                   -- the permutation has length `r`
  count (a : α) : ℓ.count a ≤ S.rep a  -- the count of `a` in the permutation is at most `S.rep a`

variable {S}

def Perm.toFin {r : ℕ} (l : Perm S r) : Fin r → α :=
  fun i ↦ l.ℓ[i]'(by simp [l.len])

@[ext]
lemma Perm.ext {r : ℕ} {l l' : Perm S r} (h : l.toFin = l'.toFin) : l = l' := by
  rcases l with ⟨l, len, count⟩
  rcases l' with ⟨l', len', count'⟩
  simp only [List.get_eq_getElem, mk.injEq] at h ⊢
  apply List.ext_get
  · rw [len, len']
  intro n H H'
  convert congr_fun h ⟨n, _⟩
  rwa [← len]

instance : Subsingleton (S.Perm 0) := ⟨fun l l' => by ext ⟨i, hi⟩; simp at hi⟩

noncomputable instance {r : ℕ} [Fintype α] : Fintype (S.Perm r) :=
    Fintype.ofInjective (fun l : S.Perm r ↦ l.toFin) fun _ _ ↦ Perm.ext

-- thm 2.4.1

lemma Perm.zero (l : S.Perm 0) : l.ℓ = [] := by
  apply List.ext_get
  · exact l.len
  intro n hn
  simp only [l.len, Nat.not_lt_zero] at hn

instance : Inhabited (S.Perm 0) := ⟨⟨[], rfl, fun _ => zero_le _⟩⟩

variable (S) in
def Perm.succOfIsFinite [inf : S.IsInfinite] (r : ℕ) : S.Perm (r + 1) ≃ (S.Perm r) × α where
  toFun l := ⟨⟨l.ℓ.tail, by simp? [l.len], fun a ↦ by
    trans ℵ₀
    · apply le_of_lt
      apply Cardinal.nat_lt_aleph0
    · exact inf.rep_infinite a⟩, l.toFin 0⟩
  invFun p :=
    { ℓ := p.1.ℓ.cons p.2
      len := by simp [p.1.len]
      count a := by
        simp only [List.count_cons, beq_iff_eq, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
          Nat.cast_zero]
        split_ifs with h
        · trans ℵ₀
          · simp only [Cardinal.add_le_aleph0, Cardinal.one_le_aleph0, and_true]
            apply le_of_lt
            exact Cardinal.nat_lt_aleph0 (List.count a p.1.ℓ)
          · exact IsInfinite.rep_infinite a
        simp only [add_zero]
        exact p.1.count a }
  left_inv l := by
    ext i
    simp only [toFin, Fin.getElem_fin, Fin.val_zero]
    induction i using Fin.induction with
    | zero => simp only [Fin.val_zero, List.getElem_cons_zero]
    | succ i ih =>
      simp only [Fin.val_succ, List.getElem_cons_succ, List.getElem_tail]
  right_inv := by
    rintro ⟨l, a⟩
    simp only [List.tail_cons, toFin, Fin.getElem_fin, Fin.val_zero, List.getElem_cons_zero]

-- thm 2.4.1
theorem Perm.count_of_infinity (r : ℕ) [Fintype α] [S.IsInfinite] :
    Fintype.card (S.Perm r) = (Fintype.card α)^r := by
  induction r with
  | zero =>
    simp only [pow_zero]
    convert Fintype.card_ofSubsingleton (default : S.Perm 0)
  | succ r ih =>
    rw [Fintype.card_congr (Perm.succOfIsFinite S r), Fintype.card_prod, ih, pow_succ]

open scoped Nat
-- thm 2.4.2
example [Fintype α] [S.IsFinite] :
    Fintype.card (S.Perm S.total) =
    (S.total !) / (∏ a : α, (S.repAsNat a) !) := sorry

end MyMultiset
