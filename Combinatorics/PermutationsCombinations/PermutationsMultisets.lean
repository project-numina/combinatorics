import Mathlib
import Combinatorics.PermutationsCombinations.Permutations

open Finset BigOperators Nat

-- definition of a list
structure MyMultiset' {α : Type} (typ : List α) (h : List.Nodup typ) where
  count : ∀ (a : α), a ∈ typ → ℵ₀

-- definition of a finset
structure MyMultiset {α : Type} (S : Finset α) where
  count : ∀ (a : α), a ∈ S → ℵ₀

-- only works for infinite repitition numbers
def permInfinity' {α : Type} {typ : List α} {h : List.Nodup typ} :
    ℕ → MyMultiset' typ h → List (List α)
| 0, _ => []
| 1, _ => typ.map fun a => [a]
| n + 1, S =>
  List.product typ (permInfinity' n S) |>.map fun (s, l) => l ++ [s]

-- this is noncomputable
noncomputable def permInfinity {α : Type} {typ : Finset α} :
    ℕ → MyMultiset typ → List (List α)
| 0, _ => [[]]
| 1, _ => typ.toList.map fun a => [a]
| n + 1, S =>
  List.product typ.toList (permInfinity n S) |>.map fun (s, l) => l ++ [s]

/--
Theorem 2.4.1: Let S be a multiset with objects of k different types, where each object has an
infinite repetition number. Then the number of r-permutations of S is k^r.
-/
theorem permInfinity'_eq_pow {α : Type} {typ : List α} {h : List.Nodup typ}
    (r : ℕ) (S : MyMultiset' typ h)  :
    (permInfinity' r S).length = typ.length ^ n := by
  sorry

theorem permInfinity_eq_pow {α : Type} {typ : Finset α}
    (r : ℕ) (S : MyMultiset typ)  :
    (permInfinity r S).length = typ.card ^ n := by
  sorry

theorem permInfinity_eq_pow_of_ge [DecidableEq α] (r : ℕ) (s : Multiset α)
    (hs : ∀ i ∈ s.toFinset, s.count i ≥ r) : (Multiset.permutationsLength r s).toFinset.card =
    s.toFinset.card ^ r := by
  sorry

/--
Theorem 2.4.2: Let $S$ be a multiset with objects of $k$ different types with finite repetition
numbers $n_1, n_2, \ldots , n_k$, respectively. Let the size of $S$ be $n = n_1 + n_2 + \cdots +
n_k$. Then the number of permutations of $S$ equals $\frac{n!}{n_1!n_2!\dots n_k!}$.
-/
theorem Multiset_sum_perm [DecidableEq α] (n : ℕ) (s : Multiset α)
    (hn : n = ∑ i ∈ s.toFinset, s.count i) : (Multiset.permutationsLength r s).toFinset.card =
    n ! / ∏ i ∈ s.toFinset, (s.count i) ! := by
  sorry


/--
Theorem 2.4.3: Let $n$ be a positive integer and let $n_1, n_2, ...,n_k$ be positive integers with
$n = n_1 + n_2 + ... + n_k$. The number of ways to partition a set of $n$ objects into $k$ labeled
boxes in which Box 1 contains $n_1$ objects, Box 2 contains $n_2$ objects, ..., Box k contains $n_k$
objects equals $\frac{n!}{n_1!n_2!\dots n_k!}$. If the boxes are not labeled, and $n_1 = n_2 =
\cdots = n_k$, then the number of partitions equals $\frac{n!}{k!n_1!n_2!\dots n_k!}$.
-/
def Multiperm {α : Type} [BEq α]:
    List ℕ → List α → List (List (List α))
| [], _ => [[]]
| a :: s, l => List.flatten ((List.sublistsLen a l).map (fun x => (List.product [x] (Multiperm s (l.diff x))).map (fun (a, b) => [a] ++ b)))

theorem partition_labeled (n k : ℕ) (x : n.Partition) (hx : x.parts.card = k) :
    (Multiperm x.parts.toList (List.range n)).length =
    n ! / ∏ i ∈ x.parts.toFinset, i ! ^ (x.parts.count i) := by
  sorry

def Multiperm_unlable {α : Type} [DecidableEq α]:
    List ℕ → List α → Finset (Multiset (List α))
| s, l => (Multiset.ofList ((Multiperm s l).map Multiset.ofList)).toFinset

theorem partition_unlabeled (n k : ℕ) (x : n.Partition) (hx : x.parts.card = k)
    (heq : ∀ i ∈ x.parts, ∀ j ∈ x.parts, i = j) :
    (Multiperm_unlable x.parts.toList (List.range n)).card =
    n ! / (k ! * ∏ i ∈ x.parts.toFinset, i ! ^ (x.parts.count i)) := by
  sorry

def label :
    List α → List (α × ℕ)
| [] => []
| x :: xs => (x, 1) :: (label xs).map (fun ⟨y, n⟩ => ⟨y, n + 1⟩)

/--
Theorem 2.4.4: There are $n$ rooks of $k$ colors with $n_1$ rooks of the first color, $n_2$ rooks of
the second color, $\ldots$, and $n_k$ rooks of the kth color. The number of ways to arrange these
rooks on an n-by-n board so that no rook can attack another $n!\frac{n!}{n_1!n_2!\cdots n_k!}=
\frac{(n!)^2}{n_1!n_2!\cdots n_k!}.$
-/
def no_attack_Multiperm {α : Type} [BEq α]:
    List ℕ → List α → List (List (List (α × ℕ)))
| s, l => List.flatten (((List.permutationsLength l.length l).map (fun x => label x)).map (fun x => Multiperm s x))

theorem partition_labeled_noattack (n k : ℕ) (x : n.Partition) (hx : x.parts.card = k) :
    (no_attack_Multiperm x.parts.toList (List.range n)).length =
    n ! * (n ! / ∏ i ∈ x.parts.toFinset, i ! ^ (x.parts.count i)) := by
  sorry
