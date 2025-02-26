import Mathlib

/--Let m and n be positive integers whose greatest common divisor is d. Prove that the greatest common divisor of the Fibonacci numbers fm and fn is the Fibonacci number fd.-/
theorem brualdi_ch7_7 (m n d : ℕ+) (hmd : d = Nat.gcd m n) :
    Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib d := by sorry
