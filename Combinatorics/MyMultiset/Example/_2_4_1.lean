import Combinatorics.MyMultiset.Perm

open MyMultiset

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

  haveI : S.IsTotallyInfinite := ⟨fun a ↦ rfl⟩

  have eq := Perm.card_of_isInfinite S 4
  simp only [Fintype.card_fin, Nat.reducePow] at eq
  have eq' := Fintype.card_congr e
  simp only [Fintype.card_coe] at eq'
  rw [eq', eq]
