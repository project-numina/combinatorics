import Combinatorics.MyMultiset.Basic

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
theorem count_of_infinity (r : ℕ) [Fintype α] [S.IsInfinite] :
    Fintype.card (S.Perm r) = (Fintype.card α)^r := by
  induction r with
  | zero =>
    simp only [pow_zero]
    convert Fintype.card_ofSubsingleton (default : S.Perm 0)
  | succ r ih =>
    rw [Fintype.card_congr (Perm.succOfIsInfinite S r), Fintype.card_prod, ih, pow_succ]

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

end Perm

end MyMultiset
