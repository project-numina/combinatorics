import Mathlib

open Real Classical

-- this is oriented
structure PreDiagonal where
  pt1 : Fin 2006
  pt2 : Fin 2006
  is_diagonal : (finRotate _)^[2] pt1 = pt2 ∨ (finRotate _)^[2] pt2 = pt1

def PreDiagonal.distinct (x : PreDiagonal) : x.pt1 ≠ x.pt2 := by
  intro h
  refine x.is_diagonal |>.recOn ?_ ?_  <;>
  · rintro (H : finRotate _ (finRotate _ _) = _)
    simp only [h, finRotate_succ_apply, Nat.reduceAdd, Fin.isValue] at H
    omega

-- we want unoriented, so we quotient
instance PreDiagonal.setoid : Setoid PreDiagonal where
  r x y := ({x.pt1, x.pt2} : Finset (Fin 2006)) = {y.pt1, y.pt2}
  iseqv :=
  { refl x := by rfl
    symm := Eq.symm
    trans := Eq.trans }

def Diagonal := Quotient (PreDiagonal.setoid)

def Diagonal.endPoints : Diagonal → (Finset (Fin 2006)) :=
  Quotient.lift (fun x => {x.pt1, x.pt2}) fun _ _ => id

@[simp]
lemma Diagonal.endPoints_preDiagonal (x : PreDiagonal) :
  Diagonal.endPoints ⟦x⟧ = {x.pt1, x.pt2} := rfl

@[simp]
lemma Diagonal.endPoints_card_eq_two (x : Diagonal) : x.endPoints.card = 2 := by
  induction x using Quotient.inductionOn with | h x =>
  simp only [endPoints_preDiagonal, Finset.card_eq_two, ne_eq]
  use x.pt1, x.pt2, x.distinct

@[simp]
lemma Diagonal.exists_pts_in_endPoints (x : Diagonal) :
    ∃ pt1 ∈ x.endPoints, ∃ pt2 ∈ x.endPoints, pt1 ≠ pt2 ∧ x.endPoints = {pt1, pt2} := by
  have := x.endPoints_card_eq_two
  rw [Finset.card_eq_two] at this
  obtain ⟨pt1, pt2, h1, h2⟩ := this
  refine ⟨pt1, ?_, pt2, ?_, h1, h2⟩ <;> rw [h2] <;> aesop

noncomputable def Diagonal.pt1 (x : Diagonal) : Fin 2006 :=
  x.exists_pts_in_endPoints.choose

lemma Diagonal.pt1_mem (x : Diagonal) : x.pt1 ∈ x.endPoints :=
  x.exists_pts_in_endPoints.choose_spec.1

noncomputable def Diagonal.pt2 (x : Diagonal) : Fin 2006 :=
  x.exists_pts_in_endPoints.choose_spec.2.choose

lemma Diagonal.pt2_mem (x : Diagonal) : x.pt2 ∈ x.endPoints :=
  x.exists_pts_in_endPoints.choose_spec.2.choose_spec.1

lemma Diagonal.pt1_neq_pt2 (x : Diagonal) : x.pt1 ≠ x.pt2 :=
  x.exists_pts_in_endPoints.choose_spec.2.choose_spec.2.1

lemma Diagonal.endPoints_eq_pt1_pt2 (x : Diagonal) : x.endPoints = {x.pt1, x.pt2} :=
  x.exists_pts_in_endPoints.choose_spec.2.choose_spec.2.2

def Diagonal.good (x : Diagonal) : Prop :=
  Odd (max x.pt1 x.pt2 - min x.pt1 x.pt2 : ℕ)

noncomputable def toPointsOnCircle (n : Fin 2006) : ℂ := Complex.exp (2 * π * Complex.I * n.1 / 2006)

-- excluding the endpoints
noncomputable def Diagonal.clockwiseArc (d : Diagonal) : Finset (Fin 2006) :=
  Finset.Ioo (min d.pt1 d.pt2) (max d.pt1 d.pt2)

def Diagonal.intersects (d d' : Diagonal) :=
  d'.endPoints ≤ d.clockwiseArc

-- if the two end points of d differ by exactly 2, then it makes an isosceles triangle with two sides
def Diagonal.IsIsoscelesByOneDiagonal (d : Diagonal) : Prop :=
    (finRotate _) ^[2] d.pt1 = d.pt2 ∨
    (finRotate _) ^[2] d.pt2 = d.pt1

structure Diagonal.IsIsoscelesByTwoDiagonal (d d' : Diagonal) where
  non_intersecting : ¬ d.intersects d'
  distinct : d ≠ d'
  shares_a_common_point : d.endPoints ⊓ d'.endPoints ≠ ∅
  isosceles :
    ∀ x ∈ d.endPoints ⊔ d'.endPoints,
    ∀ y ∈ d.endPoints ⊔ d'.endPoints,
    ∀ z ∈ d.endPoints ⊔ d'.endPoints,
      x ≠ y → x ≠ z → y ≠ z →
      dist (toPointsOnCircle x) (toPointsOnCircle y) = dist (toPointsOnCircle y) (toPointsOnCircle z) ∨
      dist (toPointsOnCircle x) (toPointsOnCircle y) = dist (toPointsOnCircle y) (toPointsOnCircle z) ∨
      dist (toPointsOnCircle x) (toPointsOnCircle z) = dist (toPointsOnCircle y) (toPointsOnCircle z)

-- if a collection of 2003 distinct diagonal are pairwise non-intersecting, they dissect the 2006-gon
structure Configuration where
  d : Fin 2003 ↪ Diagonal
  valid : ∀ i j, i ≠ j → ¬ (d i).intersects (d j)

noncomputable def Configuration.numOfIsoscelesTriangle (c : Configuration) : ℕ :=
  (∑ i : Fin 2003, if (c.d i).IsIsoscelesByOneDiagonal then 1 else 0) +
  (∑ i : Fin 2003, ∑ j : Fin 2003,
      if (c.d i).IsIsoscelesByTwoDiagonal (c.d j) then 1 else 0)

abbrev imo_2006_p2_solution : ℕ := sorry

/--
Let $P$ be a regular 2006-gon. A diagonal of $P$ is called good if its endpoints divide the boundary of $P$ into two parts, each composed of an odd number of sides of $P$. The sides of $P$ are also called good. Suppose $P$ has been dissected into triangles by 2003 diagonals, no two of which have a common point in the interior of $P$. Find the maximum number of isosceles triangles having two good sides that could appear in such a configuration.
-/
theorem imo_2006_p2 :
  IsGreatest {k | ∃ c : Configuration, c.numOfIsoscelesTriangle = k} imo_2006_p2_solution := by sorry
