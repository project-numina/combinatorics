import Mathlib

variable {n : ℕ+} (k : ℕ+)
variable (people : Fin (2*n+1) → ZMod 2) -- 0 for boys and 1 for girls

def leftNeighbors (i : Fin (2*n+1)) : Fin k → ZMod 2 :=
    fun j ↦ people <| (finRotate (2*n+1))^[j.1] i

def rightNeighbors (i : Fin (2*n+1)) : Fin k → ZMod 2 :=
    fun j ↦ people <| (finRotate (2*n+1)).symm^[j.1] i

/--
Let $n$ and $k$ be two integers with $n > k \\geqslant 1$. There are $2n+1$ students standing in a circle. Each student $S$ has $2k$ neighbours - namely, the $k$ students closest to $S$ on the right, and the $k$ students closest to $S$ on the left. Suppose that $n+1$ of the students are girls, and the other $n$ are boys. Prove that there is a girl with at least $k$ girls among her neighbours.
-/
theorem imosl_2021_c5 (h : k < n) (num_boys : (List.ofFn people).count 0 = n)
   (num_girls : (List.ofFn people).count 1 = n+1):
    ∃ (i : Fin (2*n+1)),
        people i = 1 -- this person is a girl
      ∧ ((List.ofFn (leftNeighbors k people i)).count 1 +
         (List.ofFn (rightNeighbors k people i)).count 1 >= k)
        -- number of girls among the neighbours is at least k
          := by sorry
