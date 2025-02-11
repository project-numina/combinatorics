import Combinatorics.MyMultiset.Perm


inductive MSIP
| M | S | I | P
deriving DecidableEq

instance : Fintype MSIP where
  elems := {.M, .S, .I, .P}
  complete := by intro a; cases a <;> aesop

def MSIP.toChar : MSIP → Char
  | MSIP.M => 'M'
  | MSIP.S => 'S'
  | MSIP.I => 'I'
  | MSIP.P => 'P'

open scoped Nat


structure IsPermOfMISSISSIPPI (l : List MSIP) : Prop where
  len : l.length = 11
  countM : l.count .M = 1
  countI : l.count .I = 4
  countS : l.count .S = 4
  countP : l.count .P = 2

example (s : Finset (List MSIP))
    (hs : ∀ x, x ∈ s ↔ IsPermOfMISSISSIPPI x) : s.card = 34650 := by
  let S : MyMultiset MSIP :=
  { rep := fun
    | MSIP.M => 1
    | MSIP.S => 4
    | MSIP.I => 4
    | MSIP.P => 2 }
  haveI : S.RepIsFinite := ⟨by intro a; cases a <;> aesop⟩
  have eqM : S.repAsNat MSIP.M = 1 := rfl
  have eqS : S.repAsNat MSIP.S = 4 := rfl
  have eqI : S.repAsNat MSIP.I = 4 := rfl
  have eqP : S.repAsNat MSIP.P = 2 := rfl

  let e : s ≃ S.Perm 11 :=
  { toFun l :=
      { ℓ := l.1
        len := by
          have := l.2
          rw [hs] at this
          exact this.len
        count := by
          rintro (⟨⟩|⟨⟩|⟨⟩|⟨⟩)
          · have := l.2
            rw [hs] at this
            simp [this.countM, S]
          · have := l.2
            rw [hs] at this
            simp [this.countS, S]
          · have := l.2
            rw [hs] at this
            simp [this.countI, S]
          · have := l.2
            rw [hs] at this
            simp [this.countP, S] }
    invFun p := ⟨p.1, by
      rw [hs]
      refine ⟨p.len, ?_, ?_, ?_, ?_⟩ <;>
      rw [p.count_eq_repAsNat] <;> assumption⟩
    left_inv := by intro l; rfl
    right_inv := by intro l; rfl }
  have : Fintype.card s = Fintype.card (S.Perm 11) := Fintype.card_congr e
  simp only [Fintype.card_coe] at this
  have eq : S.card = 11 := by rfl
  rw [this, ← eq,  MyMultiset.Perm.card_total]
  rw [show Finset.univ (α := MSIP) = {MSIP.M, MSIP.S, MSIP.I, MSIP.P} by rfl]
  simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_singleton, or_self, not_false_eq_true,
    Finset.prod_insert, Finset.prod_singleton, eq, eqM, eqS, eqI, eqP]
  rfl
