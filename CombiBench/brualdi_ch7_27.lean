import Mathlib

abbrev S (n : ℕ): Set ℕ := {m | (Nat.digits 10 m).length = n ∧
  (∀ i : Fin (Nat.digits 10 m).length, Odd ((Nat.digits 10 m).get i)) ∧
  Even ((Nat.digits 10 m).count 1) ∧ Even ((Nat.digits 10 m).count 3) ∧
  NeZero ((Nat.digits 10 m).count 1) ∧ NeZero ((Nat.digits 10 m).count 3)}

lemma length_eq_zero_iff (m : ℕ): (Nat.digits 10 m).length = 0 ↔ m = 0 :=
  ⟨fun h ↦ by
    simp only [Nat.reduceLeDiff, List.length_eq_zero] at h
    if h1 : m = 0 then assumption else
    have : 0 < m := by omega
    rw [Nat.digits_def' (by omega : 1 < 10) this] at h
    simp at h,
  fun _ ↦ by aesop⟩

lemma length_eq_n_if (n : ℕ) (hn1 : 2 ≤ n) (k : Fin (9 * 10^(n-1))):
  (Nat.digits 10 (10^(n - 1) + k.1)).length = n := by
  induction n with
  | zero => simp at hn1
  | succ n hn =>
    if h : n = 1 then
      subst h
      simp_rw [Nat.add_one_sub_one, Nat.pow_one]
      rw [Nat.digits_len 10 _ (by omega) (by omega)]
      simp [Nat.log_eq_iff]
      change Fin 90 at k
      rw [show 100 = 10 + 90 by rfl]
      suffices k.1 < 90 from Nat.add_lt_add_left this 10
      exact k.2
    else
    specialize hn (by omega)
    simp_rw [Nat.add_one_sub_one]
    rw [Nat.digits_len 10 _ (by omega) (by omega)]
    simp [Nat.log_eq_iff]
    change Fin (9 * 10 ^ n) at k
    have : k.1 < 9 * 10^n := by omega
    rw [show 10 ^ (n + 1) = 10 ^ n + 9 * 10 ^ n by
      nth_rw 1 [← one_mul (10 ^ n), ← add_mul]; ring]
    simp

instance (n : ℕ): Fintype {m | (Nat.digits 10 m).length = n} :=
  if hn : n = 0 then by
    subst hn; simp_rw [length_eq_zero_iff];
    simp only [Set.setOf_eq_eq_singleton];
    exact Set.fintypeSingleton 0 else
  if hn' : n = 1 then by
  subst hn'
  exact Fintype.ofBijective (α := Fin 9) (fun ⟨x, hx⟩ ↦ ⟨x + 1, by
    simp only [Set.mem_setOf_eq]
    rw [Nat.digits_len 10 _ (by omega) (by omega)]
    simp only [add_left_eq_self, Nat.log_eq_zero_iff,
      Nat.not_ofNat_le_one, or_false]
    linarith⟩) ⟨fun k1 k2 h ↦ by
      simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq,
        add_left_inj] at h
      exact Fin.eq_of_val_eq h, fun ⟨x, hx⟩ ↦ ⟨⟨x - 1, by
        simp at hx
        if hxx : x = 0 then simp [hxx] at hx else
        simp only [Nat.reduceLeDiff, Nat.digits_len 10 _ (by omega) hxx,
          add_left_eq_self, Nat.log_eq_zero_iff, Nat.not_ofNat_le_one,
          or_false] at hx
        omega⟩, if hxx : x = 0 then by simp [hxx] at hx else
          by simp [Nat.sub_one_add_one hxx]⟩⟩ else
  Fintype.ofBijective (α := Fin (9 * 10^(n-1))) (fun k ↦ ⟨10^(n-1) + k.1,
    by
      simp only [Set.mem_setOf_eq, add_pos_iff, Nat.ofNat_pos, pow_pos,
        true_or, Nat.digits_of_two_le_of_pos, List.length_cons]
      rw [length_eq_n_if n (by omega) k]⟩) ⟨fun k1 k2 h ↦ by
        simp at h ⊢
        exact Fin.eq_of_val_eq h, fun ⟨x, hx⟩ ↦
          if hx' : x = 0 then by
          simp only [Nat.reduceLeDiff, Set.mem_setOf_eq] at hx
          rw [hx'] at hx
          simp only [Nat.reduceLeDiff, Nat.digits_zero, List.length_nil] at hx
          tauto  else
          ⟨⟨x - 10^(n - 1), by
          simp only [Nat.reduceLeDiff, Set.mem_setOf_eq] at hx
          rw [Nat.digits_len 10 _ (by omega) (by omega)] at hx
          have := Nat.eq_sub_of_add_eq hx
          obtain ⟨h1, h2⟩ := Nat.log_eq_iff (by left; omega) |>.1 <|
            Nat.eq_sub_of_add_eq hx
          rw [Nat.sub_one_add_one (by omega), show 10 ^ n =
            9 * 10 ^ (n - 1) + 10 ^ (n - 1) by
            nth_rw 2 [← one_mul (10 ^ (n - 1))]
            rw [← add_mul]
            simp; exact Eq.symm (mul_pow_sub_one hn 10)] at h2
          exact Nat.sub_lt_right_of_lt_add h1 h2⟩, by
            simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq]
            simp only [Nat.reduceLeDiff, Set.mem_setOf_eq] at hx
            rw [Nat.digits_len 10 _ (by omega) (by omega)] at hx
            rw [add_comm, Nat.sub_add_cancel]
            exact (Nat.log_eq_iff (by left; omega) |>.1 <|
              Nat.eq_sub_of_add_eq hx).1⟩⟩

instance Sn_nonempty (n : ℕ) (hn : 4 ≤ n): Nonempty (S n) :=
  ⟨10^n + ∑ i ∈ Finset.Icc 3 (n-1), 5 * 10 ^ i + 133, by sorry⟩

open scoped Classical in
noncomputable instance (n : ℕ): Fintype (S n) :=
  if hn : n ∈ Finset.Icc 0 3 then sorry else
  .ofSurjective
  (α := {m | (Nat.digits 10 m).length = n})
  (fun ⟨k, hk⟩ ↦ if ∃ k' ∈ S n, k = k' then (⟨k, sorry⟩ : S n) else
  Classical.choice (α := S n) (Sn_nonempty n (by simp at hn; omega))) <|
    fun ⟨x, hx⟩ ↦ ⟨⟨x, hx.1⟩, by
      simp [hx.1, hx.2]
      simp only [Set.mem_setOf_eq, Nat.reduceLeDiff,
        List.get_eq_getElem] at hx
      intro ⟨i, hi⟩ h
      have := hx.2.1 ⟨i, hi⟩
      simp only [Nat.reduceLeDiff] at h this
      rw [← Nat.not_odd_iff_even] at h
      tauto⟩

abbrev brualdi_ch7_27_solution (n : ℕ): ℕ := sorry

/-- Determine the number of n-digit numbers with all digits odd, such that 1 and 3 each occur a nonzero, even number of times.-/
theorem brualdi_ch7_27 (n : ℕ): Fintype.card (S n) = brualdi_ch7_27_solution := sorry
