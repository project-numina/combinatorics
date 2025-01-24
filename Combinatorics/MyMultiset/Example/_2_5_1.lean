import Combinatorics.MyMultiset.Comb
import Mathlib.Tactic.DeriveFintype

namespace example_2_5_1_1

/-
Example. A bakery boasts eight varieties of doughnuts. If a box of doughnuts
contains one dozen, how many different options are there for a box of doughnuts?
-/
inductive Doughnut
| glazed | chocolate | jelly | powdered | sprinkles | creamFilled | oldFashioned | cruller
deriving DecidableEq, Fintype

def shop : MyMultiset Doughnut where
  rep _ := ⊤

instance : shop.IsTotallyInfinite := ⟨fun _ => rfl⟩

lemma card_box : Fintype.card (shop.Comb 12) = Nat.choose 19 12 := by
  rw [MyMultiset.Comb.card_of_isInfinite_ofFintype]
  rfl

end example_2_5_1_1

namespace example_2_5_1_2

noncomputable instance (r k : ℕ) : Fintype (Fin r →o Fin k) :=
  Fintype.ofInjective (OrderHom.toFun) (
    injective_of_le_imp_le OrderHom.toFun fun {x y} a ↦ a)

/-
Example. What is the number of nondecreasing sequences of length r whose terms
are taken from 1,2, ... , k?
-/
example (r k : ℕ) : Fintype.card (Fin r →o Fin k) = (k + r - 1).choose r := by
  let S : MyMultiset (Fin k) := { rep _ := ⊤ }
  haveI : S.IsTotallyInfinite := ⟨fun _ => rfl⟩
  let e₁ : (Fin r →o Fin k) ≃ (l : List (Fin k)) ×' (l.length = r ∧ List.Sorted (· ≤ ·) l) :=
  { toFun f := ⟨List.ofFn f, by simp, by
      simp only [List.sorted_le_ofFn_iff]
      exact f.2⟩
    invFun f := OrderHom.comp ⟨f.1.get, f.2.2.get_mono⟩
      (Fin.castOrderIso (by simp [f.2.1])).toOrderEmbedding.toOrderHom
    left_inv x := by ext; simp
    right_inv := by
      rintro ⟨x, ⟨h1, h2⟩⟩
      ext : 1
      · simp only [OrderHom.comp_coe, OrderHom.coe_mk, OrderEmbedding.toOrderHom_coe,
        OrderIso.coe_toOrderEmbedding]
        apply List.ext_get
        · simp [h1]
        · intro
          simp
      · exact proof_irrel_heq _ _ }
  let e₂ : S.Comb r ≃ (l : List (Fin k)) ×' (l.length = r ∧ List.Sorted (· ≤ ·) l) :=
  { toFun c := ⟨List.insertionSort (· ≤ ·) (Multiset.toList (∑ i : Fin k, (c.repAsNat i) • {i})),
      ⟨by simp [← c.card_eq, MyMultiset.fintype_card], List.sorted_insertionSort _ _⟩⟩
    invFun l :=
      { rep a := l.1.count a
        rep_fin := ⟨by aesop⟩
        obj_fin :=
          { support := { a | l.1.count a ≠ 0 }
            obj_finite := by simp
            dec := by simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and]; infer_instance }
        rep_le a := by simp [S]
        card_eq := by
          simp only [ne_eq, id_eq, eq_mpr_eq_cast]
          rw [MyMultiset.fintype_card]
          conv_rhs => rw [← l.2.1]
          rw [List.length_eq_sum_count]
          rfl }
    left_inv := by
      intro x
      ext i
      simp only
      rw [List.perm_insertionSort _ _ |>.count_eq]
      have (S : Multiset (Fin k)) (a : Fin k) : S.toList.count a = S.count a := by
        conv_rhs => rw [show S = S.toList by exact Eq.symm (Multiset.coe_toList S)]
        rw [Multiset.coe_count]
      simp [this, Multiset.count_sum', Multiset.count_singleton, MyMultiset.repAsNat_spec]
    right_inv := by
      rintro ⟨x, hx1, hx2⟩
      ext : 1
      · simp only
        apply List.eq_of_perm_of_sorted (r := (· ≤ ·))
        · refine List.perm_insertionSort (· ≤ ·) _ |>.trans ?_
          set a := _; change List.Perm a x
          suffices (a : Multiset (Fin k)) = x by
            erw [Quotient.eq'] at this
            exact this

          simp only [Multiset.coe_toList, a]
          ext i
          simp only [MyMultiset.repAsNat, Multiset.count_sum', Multiset.count_nsmul,
            Multiset.nodup_singleton, Multiset.count_singleton, mul_ite, mul_one, mul_zero,
            Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Multiset.coe_count]
          rfl
        · exact
          List.sorted_insertionSort (fun x1 x2 ↦ x1 ≤ x2) _
        · exact hx2
      · exact proof_irrel_heq _ _ }

  rw [Fintype.card_congr (e₁.trans e₂.symm),
    MyMultiset.Comb.card_of_isInfinite_ofFintype, Fintype.card_fin]

end example_2_5_1_2
