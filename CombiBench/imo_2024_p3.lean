import Mathlib

def isEventuallyPeriodic (b : ℕ → ℕ) : Prop :=
  ∃ p M, ∀ m, M ≤ m → b (m + p) = b m

/--
Let $a_1, a_2, a_3, \dots$ be an infinite sequence of positive integers,
and let $N$ be a positive integer. Suppose that, for each $n > N$,
$a_n$ is equal to the number of times $a_{n-1}$ appears in the list
$a_1, a_2, \dots, a_{n-1}$. Prove that at least one of the sequence
$a_1, a_3, a_5, \dots$ and $a_2, a_4, a_6, \dots$ is eventually periodic.
(An infinite sequence $b_1, b_2, b_3, \dots$ is eventually periodic if
there exist positive integers $p$ and $M$ such that $b_{m+p} = b_m$ for all $m \ge M$.)
-/
theorem imo_2024_p3
  (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (N : ℕ)
  (h : ∀ n > N, a n = List.count (a (n - 1)) (List.ofFn (a ∘ Fin.val (n := n -1)))) :
  (isEventuallyPeriodic (a ∘ (2 * ·))) ∨ (isEventuallyPeriodic (a ∘ (2 * · + 1))) := by sorry
