import Mathlib
import LongestPole.Main

abbrev sortedList (n : ℕ) := (List.range (2 * n))|>.map
  (fun i ↦ if i < n then 0 else 1)

def checkList (k : ℕ): List ℕ → ℕ × ℕ := fun L ↦ Id.run do
  let mut i0 := k - 1
  let mut i1 := k - 1
  for i in [k : L.length] do
    if L[i]! = L[k-1]! then
      i0 := i0 + 1 else break
  for j in [k - 1 : 0] do
    if L[j]! = L[k-1]! then
      i1 := i1 - 1 else break
  return (i0, i1)

abbrev action (n k : ℕ) : List ℕ →  List ℕ := fun L ↦ by
  obtain ⟨i0, i1⟩ := checkList k L
  exact (List.range (2 * n)).map (fun i ↦
    if i < (i1 - i0) then L[i0 + i]! else
      if (i1 - i0) ≤ i ∧ i < i1 then L[i - (i1 - i0)]!
      else L[i]!)

#eval (sortedList 2).permutations

def answer : ℕ := 0

abbrev Pairs (n : ℕ) := {x : Fin 2 → ℕ| x 0 = n ∧
    (x 1 ∈ Finset.Icc 1 (2 * n)) ∧ sorry}

noncomputable instance (n : ℕ): Fintype {x : Fin 2 → ℕ| x 0 = n ∧
    (x 1 ∈ Finset.Icc 1 (2 * n))} :=
  .ofInjective (β := Fin (2 * n))
  (fun ⟨x, ⟨hx1, hx2⟩⟩ ↦ ⟨x 1 - 1, by simp at hx2 ; omega⟩)
  (fun ⟨x, ⟨hx1, hx2⟩⟩ ⟨y, hy1, hy2⟩ hxy ↦ by
    simp at hxy hy2 hx2
    ext i ; fin_cases i <;> simp_all; omega)

noncomputable instance (n : ℕ): Fintype (Pairs n) := .ofSurjective
  (α := {x : Fin 2 → ℕ| x 0 = n ∧ (x 1 ∈ Finset.Icc 1 (2 * n))})
  (fun x ↦
  -- if sorry then ⟨x.1, ⟨x.2.1, ⟨x.2.2, sorry⟩⟩⟩ else sorry
  sorry
  ) sorry

/--
The Bank of Oslo issues two types of coin: aluminium (denoted A) and bronze (denoted B). Marianne has $n$ aluminium coins and $n$ bronze coins, arranged in a row in some arbitrary initial order. A chain is any subsequence of consecutive coins of the same type. Given a fixed positive integer $k\le 2n$, Marianne repeatedly performs the following operation: she identifies the longest chain containing the $k^{th}$ coin from the left, and moves all coins in that chain to the left end of the row. For example, if $n = 4$ and $k = 4$, the process starting from the ordering AABBBABA would be $AABBBABA \rightarrow BBBAAABA \rightarrow AAABBBBA \rightarrow BBBBAAAA \rightarrow BBBBAAAA \rightarrow \ldots$. Find all pairs $(n, k)$ with $1 \le k \le 2n$ such that for every initial ordering, at some moment during the process, the leftmost $n$ coins will all be of the same type.
-/
theorem imo_2022_p1 (n : ℕ) : Fintype.card (Pairs n) = answer := by sorry
