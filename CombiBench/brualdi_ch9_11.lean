import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs

abbrev A : Fin n → Finset (Fin n) := fun i ↦ ⊤\{i}

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

/-- Let n > 1, and let A = (A1,A2,…,An) be the family of subsets of 1,2,…,n
, where[A_{i}={1,2, \ldots, n}-{i}, \quad(i=1,2, \ldots, n)]. Prove that
A has an SDR and that the number of SDRs is the $n$th derangement number Dn.-/
theorem brualdi_ch9_11 (n : ℕ) (h_n: n > 1) : Nonempty (SDR n A) ∧
  Fintype.card (SDR n A) = n! * (∑ i : Fin n, ((-1)^i.1 : ℤ) * (1/(Nat.factorial i.1) : ℚ)):= sorry
