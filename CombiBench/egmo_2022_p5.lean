import Mathlib

def cover : ℕ → ℕ → ℕ
| _, 0 => 0
| 0, _ => 0
| n, 1 => Nat.fib (n + 1)
| n, k + 1 => Nat.fib (n + 1) * cover n k
/--
For all positive integers $n, k$, let $f(n, 2k)$ be the number of ways an $n \\times 2k$ board can be fully covered by $nk$ dominoes of size $2 \\times 1$. (For example, $f(2,2)=2$ and $f(3,2)=3$.)\nFind all positive integers $n$ such that for every positive integer $k$, the number $f(n, 2k)$ is odd.
-/
theorem egmo_2022_p5 : {n | n > 0 ∧ ∀ k > 0, Odd (cover n k)} = {x | ∃ m > 0, 2 ^ m - 1 = x} := by sorry
