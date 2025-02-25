import Mathlib

/-!copied from brualdi_ch9_11 -/

@[ext]
structure SDR (n : ℕ) (A : Fin n → Finset (Fin n)) where
  toFun : Fin n → Fin n
  mem_Ai : ∀ i, toFun i ∈ A i
  pairwise : ∀ i j, i ≠ j → toFun i ≠ toFun j

instance (n : ℕ) (A : Fin n → Finset (Fin n)): CoeFun (SDR n A) (fun _ => Fin n → Fin n) where
  coe s := s.toFun

noncomputable instance (n : ℕ) (A : Fin n → Finset (Fin n)) : Fintype (SDR n A) := by
  classical
  if h : Nonempty (SDR n A) then
    exact Fintype.ofSurjective (α := (Fin n → Fin n))
      (fun f ↦ if h1 : (∃(g : SDR n A), f = g) then ⟨f, fun i ↦ by
          rw [h1.choose_spec]; exact h1.choose.2 i, fun i j hij ↦ by
          rw [h1.choose_spec]; exact h1.choose.3 i j hij⟩
        else Classical.choice (α := (SDR n A)) h) <| fun g ↦ ⟨g, by simp⟩
  else exact fintypeOfNotInfinite (fun h1 ↦ by aesop)

abbrev A : Fin 6 → Finset (Fin 6) := fun i ↦
  if i = 1 then {1, 2} else
    if i = 2 then {2, 3} else
      if i = 3 then {3, 4} else
        if i = 4 then {4, 5} else
          if i = 5 then {5, 6} else {6, 1}

def answer : ℕ := sorry

/-- Let A = (A1, A2, A3, A4, A5, A6) where `A1 = {1,2}`,`A2 = {2,3}`, `A3 = {3,4}`,
  `A4 = {4,5}`, `A5 = {5,6}`, `A6 = {6,1}`. Determine the number of different SDRs that
  A has.-/
theorem brualdi_ch9_8 : Fintype.card (SDR 6 A) = answer := sorry
