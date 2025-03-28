import Mathlib

instance {α : Type*} [LinearOrder α] : CircularOrder α where
  btw a b c := a ≤ b ∧ b ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b
  sbtw a b c := a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
  btw_refl a := by simp
  btw_cyclic_left {a b c} := Or.rotate
  sbtw_iff_btw_not_btw {a b c} := by
    simp only [not_or, not_and_or]
    constructor
    · rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩)
      · exact ⟨.inl ⟨hab.le, hbc.le⟩, .inr hab.not_le, .inl hab.not_le, .inr hbc.not_le⟩
      · exact ⟨.inr <| .inl ⟨hbc.le, hca.le⟩, .inl hbc.not_le, .inr hca.not_le, .inl hca.not_le⟩
      · exact ⟨.inr <| .inr ⟨hca.le, hab.le⟩, .inr hab.not_le, .inr hca.not_le, .inl hca.not_le⟩
    · rintro ⟨⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩, hcb | hba, hba | hac, hac | hcb⟩
      · exact .inl ⟨hab.lt_of_not_le hba, hbc.lt_of_not_le hcb⟩
      · exact .inl ⟨hab.lt_of_not_le hba, hbc.lt_of_not_le hcb⟩
      · cases hac <| hab.trans hbc
      · cases hac <| hab.trans hbc
      · cases hac <| hab.trans hbc
      · exact .inl ⟨hab.lt_of_not_le hba, hbc.lt_of_not_le hcb⟩
      · cases hac <| hab.trans hbc
      · cases hac <| hab.trans hbc
      · cases hba <| hbc.trans hca
      · cases hba <| hbc.trans hca
      · exact .inr <| .inl ⟨hbc.lt_of_not_le hcb, hca.lt_of_not_le hac⟩
      · exact .inr <| .inl ⟨hbc.lt_of_not_le hcb, hca.lt_of_not_le hac⟩
      · cases hba <| hbc.trans hca
      · cases hba <| hbc.trans hca
      · cases hba <| hbc.trans hca
      · cases hba <| hbc.trans hca
      · cases hcb <| hca.trans hab
      · cases hcb <| hca.trans hab
      · cases hcb <| hca.trans hab
      · cases hcb <| hca.trans hab
      · exact .inr <| .inr ⟨hca.lt_of_not_le hac, hab.lt_of_not_le hba⟩
      · cases hcb <| hca.trans hab
      · exact .inr <| .inr ⟨hca.lt_of_not_le hac, hab.lt_of_not_le hba⟩
      · exact .inr <| .inr ⟨hca.lt_of_not_le hac, hab.lt_of_not_le hba⟩
  sbtw_trans_left {a b c d} := by
    rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩) (⟨hbd, hdc⟩ | ⟨hdc, hcb⟩ | ⟨hcb, hbd⟩)
    · exact .inl ⟨hab.trans hbd, hdc⟩
    · cases hbc.not_lt hcb
    · cases hbc.not_lt hcb
    · exact .inr <| .inl ⟨hdc, hca⟩
    · exact .inr <| .inl ⟨hdc, hca⟩
    · cases hbc.not_lt hcb
    · exact .inr <| .inl ⟨hdc, hca⟩
    · exact .inr <| .inl ⟨hdc, hca⟩
    · exact .inr <| .inr ⟨hca, hab.trans hbd⟩
  btw_antisymm {a b c} := by
    rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩) (⟨hcb, hba⟩ | ⟨hba, hac⟩ | ⟨hac, hcb⟩)
    · exact .inl <| hab.antisymm hba
    · exact .inl <| hab.antisymm hba
    · exact .inr <| .inl <| hbc.antisymm hcb
    · exact .inr <| .inl <| hbc.antisymm hcb
    · exact .inr <| .inr <| hca.antisymm hac
    · exact .inr <| .inr <| hca.antisymm hac
    · exact .inl <| hab.antisymm hba
    · exact .inl <| hab.antisymm hba
    · exact .inr <| .inr <| hca.antisymm hac
  btw_total {a b c} := by
    obtain hab | hba := le_total a b <;> obtain hbc | hcb := le_total b c <;>
      obtain hca | hac := le_total c a
    · exact .inl <| .inl ⟨hab, hbc⟩
    · exact .inl <| .inl ⟨hab, hbc⟩
    · exact .inl <| .inr <| .inr ⟨hca, hab⟩
    · exact .inr <| .inr <| .inr ⟨hac, hcb⟩
    · exact .inl <| .inr <| .inl ⟨hbc, hca⟩
    · exact .inr <| .inr <| .inl ⟨hba, hac⟩
    · exact .inr <| .inl ⟨hcb, hba⟩
    · exact .inr <| .inl ⟨hcb, hba⟩

variable {α : Type*} [CircularOrder α] {a b c d : α}

/-- In a circular order, the property that `a, b, c, d` are in that order. -/
def SBtw₄ (a b c d : α) : Prop := sbtw a b c ∧ sbtw c d a

lemma sbtw₄_swap : SBtw₄ a b c d ↔ SBtw₄ c d a b := and_comm

open scoped Classical Finset

variable {N : ℕ}

/-- The diagonals of the `N`-gon. -/
abbrev Diagonal (N : ℕ) := {e : Sym2 (Fin N) // ¬ e.IsDiag}

namespace Diagonal

def Intersect (d₁ d₂ : Diagonal N) : Prop :=
  Sym2.lift₂ {
    val a b c d := SBtw₄ a c b d ∨ SBtw₄ a d b c
    property a b c d := by
      simp only [eq_iff_iff]; constructor <;> rw [sbtw₄_swap, or_comm, sbtw₄_swap]
  } d₁.1 d₂.1

def Good (d : Diagonal N) : Prop :=
  Sym2.lift {
    val a b := Odd (a.val + b.val : ℕ)
    property a b := by simp [add_comm]
  } d.1

end Diagonal

-- if a collection of `2N - 3` distinct diagonal are pairwise non-intersecting, they dissect the
-- N-gon
structure TriangleDissection (N : ℕ) where
  diagonals : Fin (2 * N - 3) ↪ Diagonal N
  pairwise_not_intersect_diagonals : Pairwise fun i j ↦ ¬ (diagonals i).Intersect (diagonals j)

noncomputable def TriangleDissection.numOfIsoscelesTriangle (C : TriangleDissection N) : ℕ := by
  classical exact
  #{(a, b, c) : Fin N × Fin N × Fin N |
    ∃ (hab : a < b) (hbc : b < c),
      -- The edges of the triangle belong to the diagonals
      (∃ i, C.diagonals i = s(a, b)) ∧
      (∃ i, C.diagonals i = s(b, c)) ∧
      (∃ i, C.diagonals i = s(c, a)) ∧
      -- The triangle has two good diagonals
      ( Diagonal.Good ⟨s(a, b), by simpa using hab.ne⟩ ∧
        Diagonal.Good ⟨s(b, c), by simpa using hbc.ne⟩ ∨
        Diagonal.Good ⟨s(b, c), by simpa using hbc.ne⟩ ∧
        Diagonal.Good ⟨s(c, a), by simpa using (hab.trans hbc).ne'⟩ ∨
        Diagonal.Good ⟨s(c, a), by simpa using (hab.trans hbc).ne'⟩ ∧
        Diagonal.Good ⟨s(a, b), by simpa using hab.ne⟩) ∧
      -- The triangle has two sides of equal length
      ((b.val - a.val : ℤ) = c.val - b.val ∨
       (c.val - b.val : ℤ) = N + a.val - c.val ∨
       (N + a.val - c.val : ℤ) = c.val - b.val)}

abbrev imo_2006_p2_solution : ℕ := sorry

/--
Let $P$ be a regular 2006-gon. A diagonal of $P$ is called good if its endpoints divide the boundary of $P$ into two parts, each composed of an odd number of sides of $P$. The sides of $P$ are also called good. Suppose $P$ has been dissected into triangles by 2003 diagonals, no two of which have a common point in the interior of $P$. Find the maximum number of isosceles triangles having two good sides that could appear in such a configuration.
-/
theorem imo_2006_p2 :
    IsGreatest {k | ∃ c : TriangleDissection 2006, c.numOfIsoscelesTriangle = k}
      imo_2006_p2_solution := sorry
