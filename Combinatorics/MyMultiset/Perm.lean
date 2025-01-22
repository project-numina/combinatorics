import Combinatorics.MyMultiset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

universe u

open scoped Nat

namespace MyMultiset

variable {α β : Type u} (S : MyMultiset α)

structure Perm [DecidableEq α] (r : ℕ) where
  ℓ : List α
  len : ℓ.length = r                   -- the permutation has length `r`
  count (a : α) : ℓ.count a ≤ S.rep a  -- the count of `a` in the permutation is at most `S.rep a`

namespace Perm

variable [DecidableEq α] {S}

def toFin {r : ℕ} (l : Perm S r) : Fin r → α :=
  fun i ↦ l.ℓ[i]'(by simp [l.len])

@[ext]
lemma ext {r : ℕ} {l l' : Perm S r} (h : l.toFin = l'.toFin) : l = l' := by
  rcases l with ⟨l, len, count⟩
  rcases l' with ⟨l', len', count'⟩
  simp only [List.get_eq_getElem, mk.injEq] at h ⊢
  apply List.ext_get
  · rw [len, len']
  intro n H H'
  convert congr_fun h ⟨n, _⟩
  rwa [← len]

lemma ℓ_ext {r : ℕ} (l l' : Perm S r) : l.ℓ = l'.ℓ → l = l' := by
  intro h
  ext i
  simp only [toFin, h, Fin.getElem_fin]

instance zero_subsingleton : Subsingleton (S.Perm 0) :=
  ⟨fun l l' => by ext ⟨i, hi⟩; simp at hi⟩

noncomputable instance {r : ℕ} [Fintype α] : Fintype (S.Perm r) :=
    Fintype.ofInjective (fun l : S.Perm r ↦ l.toFin) fun _ _ ↦ Perm.ext

lemma zero (l : S.Perm 0) : l.ℓ = [] := by
  apply List.ext_get
  · exact l.len
  intro n hn
  simp only [l.len, Nat.not_lt_zero] at hn

instance : Inhabited (S.Perm 0) := ⟨⟨[], rfl, fun a => by
  simp only [List.nodup_nil, List.count_nil, Nat.cast_zero]
  exact zero_le (S.rep a)⟩⟩

variable (S) in
def succOfIsInfinite [inf : S.IsInfinite] (r : ℕ) : S.Perm (r + 1) ≃ (S.Perm r) × α where
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
def equiv [DecidableEq β] (e : α ≃ β) (r s : ℕ) (h : r = s) :
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

lemma card_eq_of_equiv [DecidableEq β] [Fintype α] [Fintype β] (e : α ≃ β) (r s : ℕ) (h : r = s) :
    Fintype.card ((S.equiv e).Perm r) = Fintype.card (S.Perm s) := by
  rwa [Fintype.card_congr (Perm.equiv ..)]

-- thm 2.4.1
variable (S) in
theorem card_of_isInfinite (r : ℕ) [Fintype α] [S.IsInfinite] :
    Fintype.card (S.Perm r) = (Fintype.card α)^r := by
  induction r with
  | zero =>
    simp only [pow_zero]
    convert Fintype.card_ofSubsingleton (default : S.Perm 0)
  | succ r ih =>
    rw [Fintype.card_congr (Perm.succOfIsInfinite S r), Fintype.card_prod, ih, pow_succ]

abbrev infiniteBooleanStream : MyMultiset Bool := ⟨fun _ ↦ ⊤⟩

def infiniteBooleanStreamPerm (n r : ℕ) (h : r + 1 ≤ n) :
    { perm : infiniteBooleanStream.Perm (n + 1) | perm.ℓ.count false = r + 1 } ≃
    { perm : infiniteBooleanStream.Perm n | perm.ℓ.count false = r + 1 } ⊕
    { perm : infiniteBooleanStream.Perm n | perm.ℓ.count false = r } where
  toFun p :=
    if h : p.1.ℓ.head (by
      intro r
      apply_fun List.length at r
      simp [p.1.len] at r) = false
    then
      .inr ⟨⟨p.1.ℓ.tail, by simp [p.1.len], by simp⟩, by
        have := p.2
        simp only [Set.mem_setOf_eq] at this ⊢
        rw [List.count_tail _ _ (by
          intro r
          apply_fun List.length at r
          simp [p.1.len] at r), if_pos (by simpa using h), this]
        rfl⟩
    else
      .inl ⟨⟨p.1.ℓ.tail, by simp [p.1.len], by simp⟩, by
        simp only [Set.mem_setOf_eq]
        rw [List.count_tail _ _ (by
          intro r
          apply_fun List.length at r
          simp [p.1.len] at r), if_neg (by aesop), p.2]
        rfl⟩
  invFun := Sum.rec
    (fun p ↦ ⟨⟨true :: p.1.ℓ, by simp [p.1.len], by simp⟩, by
      simp only [Set.mem_setOf_eq, ne_eq, Bool.false_eq_true, not_false_eq_true,
        List.count_cons_of_ne]
      exact p.2⟩)
    (fun p ↦ ⟨⟨false :: p.1.ℓ, by simp [p.1.len], by simp⟩, by
      simp only [Set.mem_setOf_eq, List.count_cons_self, add_left_inj]
      exact p.2⟩)
  left_inv := by
    rintro ⟨p, h⟩
    simp only [Set.mem_setOf_eq, Set.coe_setOf, List.length_nil, eq_mp_eq_cast] at h ⊢
    have h' : p.ℓ ≠ [] := by intro r; apply_fun List.length at r; simp [p.len] at r

    by_cases H : p.ℓ.head h' = false
    · rw [dif_pos H]
      simp only [Subtype.mk.injEq]
      refine ℓ_ext _ _ ?_
      simp only [← H, List.head_cons_tail]
    · rw [dif_neg H]
      simp only [Subtype.mk.injEq]
      refine ℓ_ext _ _ ?_
      simp only [Bool.not_eq_false] at H ⊢
      simp [← H]
  right_inv := by
    rintro (⟨p, h⟩|⟨p, h⟩)
    · simp
    · simp

lemma card_infiniteBooleanStream_perm (n r : ℕ) (h : r ≤ n) :
    Fintype.card { perm : infiniteBooleanStream.Perm n | perm.ℓ.count false = r } =
    Nat.choose n r :=
  match n with
  | 0 => by
    simp only [Set.coe_setOf]
    simp only [nonpos_iff_eq_zero] at h
    subst h
    simp only [Nat.choose_self]
    have := Perm.zero_subsingleton (S := infiniteBooleanStream)
    rw [Fintype.card_eq_one_iff]
    use ⟨⟨[], rfl, by simp⟩, by simp⟩
    intro x
    apply Subsingleton.elim
  | n+1 => match r with
    | 0 => by
      simp only [Set.coe_setOf, Nat.choose_zero_right]
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨⟨List.replicate (n + 1) true, by simp, by simp⟩, ?_⟩, ?_⟩
      · simp [List.count_replicate]
      · intro x
        refine Subtype.ext <| ℓ_ext _ _ ?_
        simp only [List.eq_replicate_iff, x.1.len, Bool.forall_bool, Bool.false_eq_true, imp_false,
          implies_true, and_true, true_and]
        intro rid
        have eq₁ : x.1.ℓ.count true = x.1.ℓ.length := by
          simp [List.length_eq_sum_count, x.2]
        rw [List.count_eq_length] at eq₁
        specialize eq₁ _ rid
        simp only [Bool.true_eq_false] at eq₁
    | r+1 => by
      rw [le_iff_eq_or_lt] at h
      rcases h with (h | h)
      · simp only [add_left_inj] at h
        subst h
        simp only [Set.coe_setOf, Nat.choose_self]
        rw [Fintype.card_eq_one_iff]
        refine ⟨⟨⟨List.replicate (r + 1) false, by simp, by simp⟩, by simp⟩, ?_⟩
        intro x
        refine Subtype.ext <| ℓ_ext _ _ ?_
        simp? [List.eq_replicate_iff, x.1.len, Bool.forall_bool, Bool.false_eq_true, imp_false,
          true_and, implies_true]
        intro rid
        have eq₁ : x.1.ℓ.count false = x.1.ℓ.length := by simp [← x.1.len, x.2]
        simp only [List.count_eq_length, Bool.false_eq, Bool.forall_bool, implies_true,
          Bool.true_eq_false, imp_false, true_and] at eq₁
        contradiction
      simp only [add_lt_add_iff_right] at h
      rw [Fintype.card_congr (infiniteBooleanStreamPerm n r (by omega))]
      rw [Fintype.card_sum, Nat.choose_succ_succ]
      rw [card_infiniteBooleanStream_perm n (r + 1) h,
        card_infiniteBooleanStream_perm n r (by omega)]
      rw [add_comm]

lemma count_eq_repAsNat [Fintype α] [S.RepIsFinite] (perm : S.Perm S.card) :
    ∀ a, perm.ℓ.count a = S.repAsNat a := by
  let A : Finset α := Finset.filter (fun a ↦ perm.ℓ.count a = S.repAsNat a) .univ
  let B : Finset α := Finset.filter (fun a ↦ perm.ℓ.count a < S.repAsNat a) .univ
  have eq : A ∪ B = .univ := by
    ext x
    have : perm.ℓ.count x ≤ S.repAsNat x := by
      rw [repAsNat, WithTop.le_untop_iff]
      exact perm.count x
    rw [le_iff_lt_or_eq] at this
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true, A, B]
    tauto
  have dis : Disjoint A B := by
    rw [Finset.disjoint_iff_inter_eq_empty, Finset.eq_empty_iff_forall_not_mem]
    intro a
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt, A,
      B]
    intro h
    rw [h]

  suffices B = ∅ by
    intro a
    have mem : a ∈ A ∪ B := eq ▸ Finset.mem_univ a
    rw [this] at mem
    simp only [Finset.union_empty, Finset.mem_filter, Finset.mem_univ, true_and, A] at mem
    assumption
  by_contra rid
  have eq₀ := perm.len
  rw [List.length_eq_sum_count] at eq₀
  have eq₁ := calc S.card
      _ = ∑ a : α, perm.ℓ.count a := eq₀.symm
      _ = ∑ a ∈ A, perm.ℓ.count a + ∑ a ∈ B, perm.ℓ.count a := by
        rw [← Finset.sum_union dis, eq]
      _ = ∑ a ∈ A, S.repAsNat a + ∑ a ∈ B, perm.ℓ.count a := by
        congr 1
        apply Finset.sum_congr rfl
        simp [A]
      _ < ∑ a ∈ A, S.repAsNat a + ∑ a ∈ B, S.repAsNat a := by
        apply add_lt_add_left
        apply Finset.sum_lt_sum_of_nonempty
        · exact Finset.nonempty_iff_ne_empty.mpr rid
        simp [B]
      _ = ∑ a : α, S.repAsNat a := by
        rw [← Finset.sum_union dis, eq]
      _ = S.card := by rw [fintype_card S]
  simp only [lt_self_iff_false] at eq₁

def insertEquiv [Fintype α] (S : MyMultiset (Option α)) [S.RepIsFinite] :
    S.Perm S.card ≃
    S.original.Perm S.original.card ×
    { perm : infiniteBooleanStream.Perm S.card | perm.ℓ.count false = S.repAsNat .none } where
  toFun perm :=
    { fst :=
      { ℓ := perm.ℓ.splitWhileRememberingPosition.2
        len := by
          have eq₁ := perm.ℓ.splitWhileRememberingPosition_fst_count_false_length_add_snd_length
          rw [perm.len] at eq₁
          simp_rw [original_card, ← eq₁,
            List.splitWhileRememberingPosition_fst_count_length, ← perm.count_eq_repAsNat .none]
          symm
          convert Nat.add_sub_cancel_left _ _
        count a := by
          rw [perm.ℓ.splitWhileRememberingPosition_snd_count a]
          simp only [original, optionType_apply]
          convert perm.count (.some a) }
      snd :=
      { val :=
        { ℓ := perm.ℓ.splitWhileRememberingPosition.1
          len := by
            rw [perm.ℓ.splitWhileRememberingPosition_fst_length, perm.len]
          count a := by simp only [le_top] }
        property := by
          simp only [Set.mem_setOf_eq, perm.ℓ.splitWhileRememberingPosition_fst_count_length]
          rw [← perm.count_eq_repAsNat .none]
          congr! } }
  invFun pair :=
  { ℓ := List.mergingWithPosition (pair.2.1.ℓ, pair.1.ℓ)
    len := by
      rw [List.mergingWithPosition_length]
      · exact pair.2.1.len
      rcases pair with ⟨item, ⟨bool, H⟩⟩
      simp only [Set.mem_setOf_eq, item.len, original_card] at H ⊢
      rw [← H, Nat.sub_eq_iff_eq_add]
      · simp_rw [← bool.len]
        simp [List.length_eq_sum_count]
      trans (S.repAsNat .none)
      · rw [H]
      · rw [fintype_card]; apply Finset.single_le_sum <;> aesop
    count := by
      rintro (⟨⟩|⟨a⟩)
      · rcases pair with ⟨item, ⟨bool, H⟩⟩
        simp only [Set.mem_setOf_eq] at H ⊢
        have eq₁ := List.mergingWithPosition_count_none (bool.ℓ, item.ℓ) (by
          simp only
          have : bool.ℓ.count true = S.original.card := by
            rw [original_card, ← H]
            simp_rw [← bool.len]
            simp [List.length_eq_sum_count]
          rw [this, item.len])
        simp only [H] at eq₁
        have ineq₁ := le_of_eq eq₁
        rw [repAsNat, WithTop.le_untop_iff] at ineq₁
        convert ineq₁
      · rcases pair with ⟨item, ⟨bool, H⟩⟩
        simp only [Set.mem_setOf_eq] at H ⊢
        have eq₁ := List.mergingWithPosition_count_some (bool.ℓ, item.ℓ) (by
          simp? [item.len, original_card, ← H]
          rw [Nat.sub_eq_iff_eq_add]
          · simp_rw [← bool.len]
            simp [List.length_eq_sum_count]
          · rw [H, fintype_card]
            apply Finset.single_le_sum <;> aesop) a
        simp only at eq₁
        have ineq₁ : item.ℓ.count a ≤ S.original.repAsNat a := by
          rw [repAsNat, WithTop.le_untop_iff]
          exact item.count a
        rw [← eq₁, repAsNat, WithTop.le_untop_iff] at ineq₁
        convert ineq₁ }
  left_inv perm := by
    simp only [Prod.mk.eta]
    apply ℓ_ext
    exact List.mergingWithPosition_splitWhileRememberingPosition _
  right_inv := by
    intro ⟨permItem, ⟨permBool, H⟩⟩
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Prod.mk.injEq, Subtype.mk.injEq]
    constructor
    · apply ℓ_ext
      simp only
      rw [List.splitWhileRememberingPosition_mergingWithPosition]
      simp only [Set.mem_setOf_eq] at H ⊢
      rw [permItem.len]
      have H' : List.count true permBool.ℓ = permBool.ℓ.length - List.count false permBool.ℓ := by
        have := List.length_eq_countP_add_countP (. = true) (permBool.ℓ)
        simp only [Bool.decide_eq_true, Bool.not_eq_true, Bool.decide_eq_false] at this
        rw [List.count_eq_countP, List.count_eq_countP]
        simp [this]
      rw [H', permBool.len, H, original_card]
    · apply ℓ_ext
      simp only
      rw [List.splitWhileRememberingPosition_mergingWithPosition]
      have H' : List.count true permBool.ℓ = permBool.ℓ.length - List.count false permBool.ℓ := by
        have := List.length_eq_countP_add_countP (. = true) (permBool.ℓ)
        simp only [Bool.decide_eq_true, Bool.not_eq_true, Bool.decide_eq_false] at this
        rw [List.count_eq_countP, List.count_eq_countP]
        simp [this]
      simp only [Set.mem_setOf_eq] at H
      simp only [permItem.len, original_card, H', permBool.len, H]

lemma insert_card [Fintype α] (S : MyMultiset (Option α)) [S.RepIsFinite]  :
    Fintype.card (S.Perm S.card) =
    Fintype.card (S.original.Perm S.original.card) *
    Nat.choose S.card (S.repAsNat .none) := by
  rw [Fintype.card_congr (insertEquiv S), Fintype.card_prod, card_infiniteBooleanStream_perm,
    fintype_card]
  rw [fintype_card]
  apply Finset.single_le_sum
  · simp
  · simp

theorem card_total' [Fintype α] [S.RepIsFinite] :
    Fintype.card (S.Perm S.card) * (∏ a : α, (S.repAsNat a) !) =
    (S.card !) := by
  classical
  convert Fintype.induction_empty_option
    (P := fun β (_ : Fintype β) ↦
      ∀ (S : MyMultiset β) (_ : S.RepIsFinite),
        letI : DecidableEq β := Classical.decEq β
        Fintype.card (S.Perm S.card) * (∏ a : β, (S.repAsNat a) !) =
    (S.card !)) ?_ ?_ ?_ α S inferInstance
  · intro α β _ e ih S _
    letI : Fintype α := Fintype.ofEquiv β e.symm
    -- haveI : DecidableEq α := Equiv.decidableEq e
    have eq1 := ih (S.equiv e.symm) inferInstance
    convert eq1 using 2
    · symm
      convert Perm.card_eq_of_equiv .. using 1
      convert equiv_card ..
      exact Subsingleton.elim _ _
    · symm
      apply Fintype.prod_bijective e e.bijective
      intro a
      congr 1
    · symm; convert equiv_card ..; exact Subsingleton.elim _ _
  · intro T h
    erw [card_empty]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, Nat.factorial_zero]
    convert Fintype.card_ofSubsingleton default
    · infer_instance
    · infer_instance

  intro α _ ih S _
  have := congr($(insert_card S) * ∏ a : Option α, (S.repAsNat a)!)
  convert this using 1
  · congr!
  rw [mul_assoc, mul_comm _ (∏ _, _), ← mul_assoc]
  have eq₁ := ih S.original inferInstance
  rw [← original_card', ← Nat.factorial_mul_ascFactorial]
  convert congr($eq₁.symm * (S.original.card + 1).ascFactorial S.single.card) using 1
  · congr!; exact Subsingleton.elim _ _
  simp only [Fintype.prod_option]
  simp only [mul_assoc]
  congr 1
  · congr!; exact Subsingleton.elim _ _

  simp only [original_repAsNat_eq, ← mul_assoc]
  rw [mul_comm _ (∏ _, _)]
  simp only [single_card, mul_assoc, mul_eq_mul_left_iff]
  left
  erw [Nat.add_choose, ← Nat.mul_div_assoc]
  · symm
    apply Nat.eq_div_of_mul_eq_left
    · simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨Nat.factorial_ne_zero _, Nat.factorial_ne_zero _⟩
    · conv_lhs => rw [mul_comm, mul_comm (S.original.card !), mul_assoc,
        Nat.factorial_mul_ascFactorial]
  · exact Nat.factorial_mul_factorial_dvd_factorial_add _ _

-- theorem 2.4.2
theorem card_total [Fintype α] [S.RepIsFinite] :
    Fintype.card (S.Perm S.card) =
    (S.card !) / (∏ a : α, (S.repAsNat a) !) := by
  rw [← card_total']
  rw [Nat.mul_div_cancel]
  rw [Nat.pos_iff_ne_zero]
  intro r
  rw [Finset.prod_eq_zero_iff] at r
  obtain ⟨_, ⟨_, ha⟩⟩ := r
  exact Nat.factorial_ne_zero _ ha

end Perm

end MyMultiset
