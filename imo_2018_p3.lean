import Mathlib





def anti_pascal_triangle : List ℤ → List (ℤ × List ℤ)
  | [] => []
  | x :: xs => (x, xs) :: (anti_pascal_triangle xs).map (fun y => y)

#eval anti_pascal_triangle [4,5,1,2]


def first_element : List ℤ → ℤ
 | [] => 0
 | x :: _ => x  -- 获取列表的第一个元素


def anti_pascal_triangle_first (l: List ℤ): List ℤ :=
match l with
| [] => []
| x :: xs =>
  (
    List.dropLast (
      (anti_pascal_triangle (x :: xs)).map (fun ⟨x, xs⟩ => abs (x - xs.headD 0))
    )
  )

#eval anti_pascal_triangle_first [4,5,1,2]



def anti_pascal_triangle_aux (l: List ℤ): List (List ℤ) :=
match l with
| [] => []
| x :: xs =>
  let l' := anti_pascal_triangle_first (x :: xs)
  l' :: (anti_pascal_triangle_aux l')
termination_by l.length
decreasing_by
  clear l'
  simp [anti_pascal_triangle_first]
  unfold anti_pascal_triangle
  simp
  induction xs
  · simp [anti_pascal_triangle]
  · simp
    simp [anti_pascal_triangle]
    assumption

#eval anti_pascal_triangle_aux [5, 4, 6, 2]

def anti_pascal_triangle' (l: List ℤ): List (List ℤ) := l :: List.dropLast (anti_pascal_triangle_aux l)

#eval anti_pascal_triangle' [5, 4, 6, 2]

def flaten : List (List ℤ) → List ℤ
  | [] => []
  | x :: xs => x ++ flaten xs


#eval flaten (anti_pascal_triangle' [5, 4, 6, 2])

/--
An anti-Pascal triangle is an equilateral triangular array of numbers such that,
 except for the numbers in the bottom row, each number is the absolute value of the difference of
  the two numbers immediately below it. For example, the following is an anti-Pascal triangle with
  four rows which contains every integer from $1$ to $10$ \[4\]\[2\quad 6\]\[5\quad 7 \quad 1\]
  \[8\quad 3 \quad 10 \quad 9\] Does there exist an anti-Pascal triangle with $2018$ rows which
   contains every integer from $1$ to $1 + 2 + 3 + \dots + 2018$?
-/
theorem imo_2018_p3 : ∃ l , (anti_pascal_triangle' l).length = 2018
    ∧ flaten (anti_pascal_triangle' l) ⊆  List.Ico 1 (List.sum (List.Ico 1 2018)) := by
  sorry
