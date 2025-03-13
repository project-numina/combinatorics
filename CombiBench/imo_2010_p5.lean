import Mathlib

-- Ture

structure Bottles where
  (B1 B2 B3 B4 B5 B6 : ℕ)

def op11 : Bottles → Bottles
| ⟨b1, b2, b3, b4, b5, b6⟩ => ⟨b1 - 1, b2 + 2, b3, b4, b5, b6⟩

def op12 : Bottles → Bottles
| ⟨b1, b2, b3, b4, b5, b6⟩ => ⟨b1, b2 - 1, b3 + 2, b4, b5, b6⟩

def op13 : Bottles → Bottles
| ⟨b1, b2, b3, b4, b5, b6⟩ => ⟨b1, b2, b3 - 1, b4 + 2, b5, b6⟩

def op14 : Bottles → Bottles
| ⟨b1, b2, b3, b4, b5, b6⟩ => ⟨b1, b2, b3, b4 - 1, b5 + 2, b6⟩

def op15 : Bottles → Bottles
| ⟨b1, b2, b3, b4, b5, b6⟩ => ⟨b1, b2, b3, b4, b5 - 1, b6 + 2⟩

def op21 : Bottles → Bottles
| ⟨b1, b2, b3, b4, b5, b6⟩ => ⟨b1 - 1, b3, b2, b4, b5, b6⟩

def op22 : Bottles → Bottles
| ⟨b1, b2, b3, b4, b5, b6⟩ => ⟨b1, b2 - 4, b4, b3, b5, b6⟩

def op23 : Bottles → Bottles
| ⟨b1, b2, b3, b4, b5, b6⟩ => ⟨b1, b2, b3 - 1, b5, b4, b6⟩

def op24 : Bottles → Bottles
| ⟨b1, b2, b3, b4, b5, b6⟩ => ⟨b1, b2, b3, b4 - 1, b6, b5⟩

inductive OP
| op11 | op12 | op13 | op14 | op15 | op21 | op22 | op23 | op24

def apply_op : OP → (Bottles → Bottles)
| OP.op11 => op11
| OP.op12 => op12
| OP.op13 => op13
| OP.op14 => op14
| OP.op15 => op15
| OP.op21 => op21
| OP.op22 => op22
| OP.op23 => op23
| OP.op24 => op24

def init : Bottles := ⟨1, 1, 1, 1, 1, 1⟩

def seq : List OP := sorry

abbrev imo_2010_p5_solution : Prop := sorry

/--
Each of the six boxes $B_1$, $B_2$, $B_3$, $B_4$, $B_5$, $B_6$ initially contains one coin. The following operations are allowed: Type 1) Choose a non-empty box $B_j$, $1\leq j \leq 5$, remove one coin from $B_j$ and add two coins to $B_{j+1}$; Type 2) Choose a non-empty box $B_k$, $1\leq k \leq 4$, remove one coin from $B_k$ and swap the contents (maybe empty) of the boxes $B_{k+1}$ and $B_{k+2}$. Determine if there exists a finite sequence of operations of the allowed types, such that the five boxes $B_1$, $B_2$, $B_3$, $B_4$, $B_5$ become empty, while box $B_6$ contains exactly $2010^{2010^{2010}}$ coins.
-/
theorem imo_2010_p5 :
  ((seq.map apply_op).foldl (· ∘ ·) id init = ⟨0, 0, 0, 0, 0, _2010 ^ (2010 ^ 2010)⟩) =
  imo_2010_p5_solution := by sorry
