import Mathlib

open Finset Set

structure SDR (n : ℕ) (A : Fin n → Finset α) where
  toFun : Fin n → α
  mem_Ai : ∀ i, toFun i ∈ A i
  pairwise : ∀ i j, i ≠ j → toFun i ≠ toFun j

instance (n : ℕ) (A : Fin n → Finset α) : CoeFun (SDR n A) (fun _ => Fin n → α) where
  coe s := s.toFun

noncomputable instance (n : ℕ) (A : Fin n → Finset ℕ) : Fintype (SDR n A) := by
  classical
  let Y := Finset.biUnion (@Finset.univ (Fin n) _) A
  if h : Nonempty (SDR n A) then
    exact Fintype.ofSurjective (α := (Fin n → Y))
      (fun f ↦ if h1 : (∃(g : SDR n A), ∀ i, f i = g i) then ⟨fun i => f i,
          fun i ↦ by have ⟨g, hg⟩ := h1; simp [hg, g.mem_Ai],
          fun i j hij ↦ by have ⟨g, hg⟩ := h1; simp [hg, g.pairwise i j hij]⟩
        else Classical.choice (α := (SDR n A)) h) <| fun g ↦
          ⟨fun i => ⟨g i, by simp [Y]; use i; simp [g.mem_Ai]⟩, by
            simp; suffices ∃ (g' : SDR n A), ∀ (i : Fin n), g.toFun i = g'.toFun i by simp [this]
            use g; simp⟩
  else exact fintypeOfNotInfinite (fun h1 ↦ by aesop)

abbrev A : Fin 6 → Finset ℕ := fun i ↦ match i with
  | 1 => {1, 2}
  | 2 => {2, 3}
  | 3 => {3, 4}
  | 4 => {4, 5}
  | 5 => {5, 6}
  | 6 => {6, 1}

abbrev brualdi_ch9_8_solution : ℕ := sorry

/--
Let A = (A1, A2, A3, A4, A5, A6) where `A1 = {1,2}`,`A2 = {2,3}`, `A3 = {3,4}`, `A4 = {4,5}`, `A5 = {5,6}`, `A6 = {6,1}`. Determine the number of different SDRs that A has.
-/
theorem brualdi_ch9_8 : Fintype.card (SDR 6 A) = brualdi_ch9_8_solution := by sorry
