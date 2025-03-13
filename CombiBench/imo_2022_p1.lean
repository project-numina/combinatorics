import Mathlib

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

abbrev action (n k : ℕ) : List ℕ → List ℕ := fun L ↦
   (List.range ((checkList k L).2 - (checkList k L).1)).map (fun i ↦ L[(checkList k L).1 + i - 1]!) ++
     (List.range (checkList k L).1).map (fun i ↦ L[i - 1]!) ++
     (List.range (2 * n - (checkList k L).2)).map (fun i ↦ L[(checkList k L).2 + i - 1]!)

 abbrev pown (n m k: ℕ) : List ℕ → List ℕ := fun L ↦ Id.run do
   let mut L' := L
   for _ in [0 : m-1] do
     L' := action n k L'
   return L'

 abbrev checkLeft (n : ℕ) : List ℕ → Bool := fun L ↦ Id.run do
   for i in [0 : n] do
     if L[i]! ≠ L[0]! then
       return false
     else continue
   return true

 #eval (sortedList 2).permutations

 def answer : ℕ := 0

abbrev Pairs (n k: ℕ) := {x : Fin 2 → ℕ| x 0 = n ∧
     (x 1 ∈ Finset.Icc 1 (2 * n)) ∧ (∃ (m : ℕ),
     (checkLeft n (pown n m k (sortedList n))))}

 noncomputable instance (n : ℕ): Fintype {x : Fin 2 → ℕ| x 0 = n ∧
     (x 1 ∈ Finset.Icc 1 (2 * n))} :=
   .ofInjective (β := Fin (2 * n))
   (fun ⟨x, ⟨hx1, hx2⟩⟩ ↦ ⟨x 1 - 1, by simp at hx2 ; omega⟩)
   (fun ⟨x, ⟨hx1, hx2⟩⟩ ⟨y, hy1, hy2⟩ hxy ↦ by
     simp at hxy hy2 hx2
     ext i ; fin_cases i <;> simp_all; omega)

instance [NeZero n]: Nonempty (Pairs n k) := ⟨![n, 1],
     ⟨rfl, by simpa using NeZero.one_le, ⟨0, by
       simp [pown, checkLeft]; sorry⟩⟩⟩

 open scoped Classical in
 noncomputable instance (n : ℕ) [NeZero n]: Fintype (Pairs n k) := .ofSurjective
  (α := {x : Fin 2 → ℕ| x 0 = n ∧ (x 1 ∈ Finset.Icc 1 (2 * n))})
  (fun x ↦ if h : ((∃ (m : ℕ),
    (checkLeft n (pown n m k (sortedList n))))) then ⟨x.1, ⟨x.2.1, ⟨x.2.2, h⟩⟩⟩
    else Classical.choice inferInstance) <|
  fun x ↦ ⟨⟨x.1, ⟨x.2.1, x.2.2.1⟩⟩, by simp [x.2.2.2]⟩

 /--
 The Bank of Oslo issues two types of coin: aluminium (denoted A) and bronze (denoted B). Marianne has $n$ aluminium coins and $n$ bronze coins, arranged in a row in some arbitrary initial order. A chain is any subsequence of consecutive coins of the same type. Given a fixed positive integer $k\le 2n$, Marianne repeatedly performs the following operation: she identifies the longest chain containing the $k^{th}$ coin from the left, and moves all coins in that chain to the left end of the row. For example, if $n = 4$ and $k = 4$, the process starting from the ordering AABBBABA would be $AABBBABA \rightarrow BBBAAABA \rightarrow AAABBBBA \rightarrow BBBBAAAA \rightarrow BBBBAAAA \rightarrow \ldots$. Find all pairs $(n, k)$ with $1 \le k \le 2n$ such that for every initial ordering, at some moment during the process, the leftmost $n$ coins will all be of the same type.
 -/
 theorem imo_2022_p1 (n : ℕ) [NeZero n]:
     Fintype.card (Pairs n k) = answer := by sorry
