import Mathlib

universe u v w

theorem thm3_1_1 {α : Type u} {β : Type v} [DecidableEq β] {s : Finset α} {t : Finset β}
    {f : α → β} (hf : ∀ a ∈ s, f a ∈ t) (hs : (s.image f).card < s.card) :
    ∃ y ∈ t, 1 < (Finset.filter (fun x ↦ f x = y) s).card := by
  by_contra! h
  have h' : ∀ y ∈ Finset.image f s, (Finset.filter (fun x ↦ f x = y) s).card ≤ 1 := by
    intro y hy
    suffices Finset.image f s ⊆ t by tauto
    exact Finset.image_subset_iff.mpr hf
  have h1 := Finset.card_le_mul_card_image s 1 h'
  linarith
