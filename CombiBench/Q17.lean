import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.Symmetric
universe u

/-!
A Latin square of order $n$ (based on $Z_{n}$) is idempotent,
provided that its entries on the diagonal running from upper left to
lower right are $0,1,2,\ldots,n-1$.\\
(1) Construct an example of an idempotent Latin square of order 5.\\
(2) Construct an example of a symmetric, idempotent Latin square of order 5.
-/

structure LatinSquare (n : ℕ) where
  carrier : Matrix (Fin n) (Fin n) (ZMod n)
  pairwise_1 : ∀ i j1 j2, j1 ≠ j2 → carrier i j1 ≠ carrier i j2
  pairwise_2 : ∀ j i1 i2, i1 ≠ i2 → carrier i1 j ≠ carrier i2 j

instance : CoeSort (LatinSquare n) (Type) where
  coe _ := Matrix (Fin n) (Fin n) (ZMod n)

lemma IsIdem_of_diag_sorted: ∀ (n : ℕ) (L : LatinSquare n),
  (∀ i, L.1 i i = i.1) → IsIdempotentElem L.1 := sorry

theorem Q17_i : ∃ L : LatinSquare 5, IsIdempotentElem L.1 := sorry

theorem Q17_ii : ∃ L : LatinSquare 5, IsIdempotentElem L.1 ∧ L.1.IsSymm := sorry
