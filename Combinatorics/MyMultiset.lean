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

lemma Perm.ℓ_ext {r : ℕ} (l l' : Perm S r) : l.ℓ = l'.ℓ → l = l' := by
  intro h
  ext i
  simp only [toFin, h, Fin.getElem_fin]

instance perm_zero_subsingleton : Subsingleton (S.Perm 0) :=
  ⟨fun l l' => by ext ⟨i, hi⟩; simp at hi⟩

noncomputable instance {r : ℕ} [Fintype α] : Fintype (S.Perm r) :=
    Fintype.ofInjective (fun l : S.Perm r ↦ l.toFin) fun _ _ ↦ Perm.ext

lemma Perm.zero (l : S.Perm 0) : l.ℓ = [] := by
  apply List.ext_get
  · exact l.len
  intro n hn
  simp only [l.len, Nat.not_lt_zero] at hn

instance : Inhabited (S.Perm 0) := ⟨⟨[], rfl, fun a => by
  simp only [List.nodup_nil, List.count_nil, Nat.cast_zero]
  exact zero_le (S.rep a)⟩⟩

variable (S) in
def Perm.succOfIsInfinite [inf : S.IsInfinite] (r : ℕ) : S.Perm (r + 1) ≃ (S.Perm r) × α where
  toFun l := ⟨⟨l.ℓ.tail, by simp? [l.len], fun a ↦ by
    rw [inf.rep_infinite]
    exact OrderTop.le_top _⟩, l.toFin 0⟩
  invFun p :=
    { ℓ := p.1.ℓ.cons p.2
      len := by simp [p.1.len]
      count a := by
        rw [inf.rep_infinite]
        exact OrderTop.le_top _ }
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


@[simps]
def Perm.equiv [DecidableEq β] (e : α ≃ β) (r s : ℕ) (h : r = s) :
    (S.equiv e).Perm r ≃ S.Perm s where
  toFun l :=
  { ℓ := l.ℓ.map e.symm
    len := by simp [h, l.len]
    count a := by
      rw [show a = e.symm (e a) by simp]
      rw [List.count_eq_countP, List.countP_map]
      simp only [Equiv.symm_apply_apply, equiv_apply]
      have := l.count (e a)
      simp only [equiv_apply, comap_rep, Equiv.symm_apply_apply, List.count_eq_countP] at this
      convert this using 3
      aesop }
  invFun l :=
  { ℓ := l.ℓ.map e
    len := by simp [h, l.len]
    count b := by
      rw [show b = e (e.symm b) by simp]
      rw [List.count_eq_countP, List.countP_map]
      simp only [Equiv.apply_symm_apply, equiv_apply, comap_rep]
      have := l.count (e.symm b)
      simp only [List.count_eq_countP] at this
      convert this using 3
      aesop }
  left_inv l := by ext; simp [Perm.toFin]
  right_inv l := by ext; simp [Perm.toFin]

lemma Perm.card_eq_of_equiv [DecidableEq β] [Fintype α] [Fintype β] (e : α ≃ β) (r s : ℕ) (h : r = s) :
    Fintype.card ((S.equiv e).Perm r) = Fintype.card (S.Perm s) := by
  rwa [Fintype.card_congr (Perm.equiv ..)]

-- thm 2.4.1
variable (S) in
theorem Perm.count_of_infinity (r : ℕ) [Fintype α] [S.IsInfinite] :
    Fintype.card (S.Perm r) = (Fintype.card α)^r := by
  induction r with
  | zero =>
    simp only [pow_zero]
    convert Fintype.card_ofSubsingleton (default : S.Perm 0)
  | succ r ih =>
    rw [Fintype.card_congr (Perm.succOfIsInfinite S r), Fintype.card_prod, ih, pow_succ]

lemma example_2_4_1 (s : Finset ℕ) (hs : ∀ x, x ∈ s ↔ (Nat.digits 3 x).length ≤ 4) : s.card = 81 := by
  let S : MyMultiset (Fin 3) := { rep _ := ⊤ }
  let e : s ≃ S.Perm 4 :=
  { toFun x :=
    { ℓ := (Nat.digits 3 x.1).map (↑) |>.fillToLength 4 0
      len := by
        rw [List.length_fillToLength]
        rw [List.length_map, ← hs]
        exact x.2
      count a := by simp [S] }
    invFun l := ⟨Nat.ofDigits 3 (l.ℓ.map Fin.val |>.dropWhileRight (· = 0)), by
      rw [hs, Nat.digits_ofDigits]
      · refine (l.ℓ.map Fin.val).dropWhileRight_length _ |>.trans ?_
        simp only [List.length_map, l.len, le_refl]
      · omega
      · intro x hx
        simp? [List.dropWhileRight] at hx
        have m := List.dropWhile_sublist _ |>.mem hx
        simp only [List.mem_reverse, List.mem_map] at m
        obtain ⟨a, ha, rfl⟩ := m
        exact a.2
      · intro h
        have := (l.ℓ.map Fin.val).dropWhileRight_getLast_not (fun a ↦ a = 0) h
        simpa using this⟩
    left_inv x := by
      ext : 1
      have eq : List.map (Fin.val (n := 3) ∘ Nat.cast) (Nat.digits 3 x.1) = Nat.digits 3 x.1 := by
        apply List.ext_getElem
        · simp
        · intro n hn hn'
          simp only [Nat.reduceLeDiff, List.getElem_map, Function.comp_apply, Fin.val_natCast,
            Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
          exact Nat.digits_lt_base (by omega) <| (Nat.digits 3 x.1).getElem_mem _
      simp [Nat.ofDigits_normalize, List.fillToLength, Nat.ofDigits_append, eq, Nat.ofDigits_digits]

    right_inv l := by
      apply Perm.ℓ_ext
      simp only [Nat.ofDigits_normalize, Nat.reduceLeDiff, Nat.one_lt_ofNat, List.mem_map,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Fin.is_lt, implies_true,
        Nat.digits_ofDigits', Fin.isValue]
      apply List.ext_getElem
      · rw [l.len, List.length_fillToLength (h := by
          simpa only [List.length_map] using List.dropWhileRight_length _ _ |>.trans
            (by simp [l.len]))]
      · intro n hn hn'
        simp_rw [← List.dropWhileRight_map, List.map_map]
        have eq (x : List _) (hx : List.Sublist x l.ℓ) :
            List.map (Nat.cast ∘ Fin.val (n := 3)) x = x := by
          apply List.ext_getElem
          · simp
          · intro n hn hn'
            simp only [List.getElem_map, Function.comp_apply, Fin.cast_val_eq_self]
        simp_rw [eq _ (l.ℓ.dropWhileRight_sublist ((· = 0) ∘ Fin.val))]
        simp_rw [show (fun n : ℕ ↦ decide (n = 0)) ∘ Fin.val (n := 3) = (fun n : Fin 3 ↦ n = 0) by
          ext; aesop]
        simp_rw [l.len ▸ l.ℓ.dropWhileRight_eq_fillToLength 0] }

  haveI : S.IsInfinite := ⟨fun a ↦ rfl⟩

  have eq := Perm.count_of_infinity S 4
  simp only [Fintype.card_fin, Nat.reducePow] at eq
  have eq' := Fintype.card_congr e
  simp only [Fintype.card_coe] at eq'
  rw [eq', eq]

#print axioms example_2_4_1

example [Fintype α] [S.IsFinite] :
    Fintype.card (S.Perm S.total) =
    (S.total !) / (∏ a : α, (S.repAsNat a) !) := by
  classical
  convert Fintype.induction_empty_option
    (P := fun β : Type u ↦ ∀ (T : MyMultiset β) [T.IsFinite], Fintype.card (T.Perm T.total) =
      T.total ! / ∏ a : β, (T.repAsNat a)!)
    (by
      intro α β _ e ih S _
      letI : Fintype α := Fintype.ofEquiv β e.symm
      have eq1 := ih (S.equiv e.symm)
      rw [Perm.card_eq_of_equiv (h := equiv_total ..), equiv_total] at eq1
      rw [eq1]
      congr 1
      apply Fintype.prod_bijective e e.bijective
      intro a
      congr 1)
    (by
      intro T h
      simp only [total_empty, Nat.factorial_zero, Finset.univ_eq_empty, Finset.prod_empty,
        zero_lt_one, Nat.div_self]
      convert Fintype.card_ofSubsingleton default
      · infer_instance
      · infer_instance)
    (by
      intro α _ ih S _
      sorry) α S

end MyMultiset
