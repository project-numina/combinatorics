import Mathlib.Data.Finset.Card

namespace List

variable {α : Type}

def combinationsUnboundedAux : List α → List (α × List α)
  | [] => []
  | x :: xs => (x, x :: xs) :: combinationsUnboundedAux xs

def combinationsUnbounded : ℕ → List α → List (List α)
  | 0, _ => [[]]
  | r + 1, l => List.flatten ((combinationsUnboundedAux l).map (fun ⟨x, xs⟩ => (combinationsUnbounded r xs).map (List.cons x)))

inductive AllowRepeat (α : Type)
 | finite (x : α)
 | infinite (x : α)

def combinationsUnboundedAux' : List (AllowRepeat α) → List (α × List (AllowRepeat α))
  | [] => []
  | x :: xs => match x with
    | AllowRepeat.finite y => (y, xs) :: combinationsUnboundedAux' xs
    | AllowRepeat.infinite y => (y, x :: xs) :: combinationsUnboundedAux' xs

def combinationsUnbounded' : ℕ → List (AllowRepeat α) → List (List α)
  | 0, _ => [[]]
  | r + 1, l => List.flatten ((combinationsUnboundedAux' l).map (fun ⟨x, xs⟩ => (combinationsUnbounded' r xs).map (List.cons x)))

#eval List.combinationsUnbounded' 3 [AllowRepeat.infinite 1, AllowRepeat.infinite 1, AllowRepeat.finite 2, AllowRepeat.finite 2, AllowRepeat.finite 3]

end List
