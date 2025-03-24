import Mathlib

open Function

structure FrogSystem (N : ℕ) where
  points : {e : Sym2 (Fin N) // ¬ e.IsDiag} → EuclideanSpace ℝ (Fin 2)

  segments (s t : Fin N) : {e : Sym2 (Fin N) // ¬ e.IsDiag}
  mem_segments (s t : Fin N) : i ∈ (segments i t).1

def FrogSystem.GeoffsWish (F : FrogSystem N) : Prop := ∀ t, Injective fun s ↦ F.segments s t

/--
There are $n\ge 2$ line segments in the plane such that every two segments cross and no three segments meet at a point. Geoff has to choose an endpoint of each segment and place a frog on it facing the other endpoint. Then he will clap his hands $n-1$ times. Every time he claps, each frog will immediately jump forward to the next intersection point on its segment. Frogs never change the direction of their jumps. Geoff wishes to place the frogs in such a way that no two of them will ever occupy the same intersection point at the same time. (a) Prove that Geoff can always fulfill his wish if $n$ is odd. (b) Prove that Geoff can never fulfill his wish if $n$ is even.
-/
theorem imo_2016_p6 :
    -- If `n ≥ 2` is odd, then Geoff can always fulfill his wish.
    (∀ n ≥ 2, Odd n → ∃ F : FrogSystem n, F.GeoffsWish) ∧
    -- If `n ≥ 2` is even, then Geoff can never fulfill his wish.
      ∀ n ≥ 2, Even n → ∀ F : FrogSystem n, ¬ F.GeoffsWish := sorry
