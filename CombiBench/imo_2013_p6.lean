import Mathlib

def M (n : ℕ) : ℕ := sorry

def N (n : ℕ) : ℕ :=
  (Finset.product (Finset.Icc 1 n) (Finset.Icc 1 n) |>.filter
  (fun ⟨x, y⟩ => x + y ≤ n ∧ Nat.gcd x y = 1)).card

/--
Let $n \ge 3$ be an integer, and consider a circle with $n + 1$ equally spaced points marked on it. Consider all labellings of these points with the numbers $0, 1, ... , n$ such that each label is used exactly once; two such labellings are considered to be the same if one can be obtained from the other by a rotation of the circle. A labelling is called beautiful if, for any four labels $a < b < c < d$ with $a + d = b + c$, the chord joining the points labelled $a$ and $d$ does not intersect the chord joining the points labelled $b$ and $c$. Let $M$ be the number of beautiful labelings, and let N be the number of ordered pairs $(x, y)$ of positive integers such that $x + y \le n$ and $\gcd(x, y) = 1$. Prove that\[ M = N + 1.\]
-/
theorem imo_2013_p6 (n : ℕ) (hn : n ≥ 3) : M n = N n + 1 := by sorry
