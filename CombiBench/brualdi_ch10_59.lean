import Mathlib

structure LatinSquare (n : ℕ) where
  carrier : Matrix (Fin n) (Fin n) (ZMod n)
  pairwise_1 : ∀ i j1 j2, j1 ≠ j2 → carrier i j1 ≠ carrier i j2
  pairwise_2 : ∀ j i1 i2, i1 ≠ i2 → carrier i1 j ≠ carrier i2 j
/--
A Latin square of order $n$ (based on $Z_{n}$) is idempotent, provided that its entries on the diagonal running from upper left to lower right are $0,1,2,\ldots,n-1$.\\ (1) Construct an example of an idempotent Latin square of order 5.\\ (2) Construct an example of a symmetric, idempotent Latin square of order 5.
-/
theorem brualdi_ch10_59 : ∃ L : LatinSquare 5, IsIdempotentElem L.1 ∧
    ∃ L : LatinSquare 5, IsIdempotentElem L.1 ∧ L.1.IsSymm := sorry
