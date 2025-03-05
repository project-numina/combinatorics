import Mathlib

def eraseIdxs : List α → List (Fin n) → List α :=
  List.foldl (fun currentList idxToBeRemoved => currentList.eraseIdx idxToBeRemoved)

/--
An integer $N \ge 2$ is given. A collection of $N(N + 1)$ soccer players, no two of whom are of the same height, stand in a row. Sir Alex wants to remove $N(N - 1)$ players from this row leaving a new row of $2N$ players in which the following $N$ conditions hold: ($1$) no one stands between the two tallest players, ($2$) no one stands between the third and fourth tallest players, $\cdots$ ($N$) no one stands between the two shortest players. Show that this is always possible.
-/
theorem imo_2017_p5 (N : ℕ) (h_N: N ≥ 2) (heights: List ℝ)
  (length: heights.length = N * (N + 1))
  (distinct_heights: heights.Nodup) :
  ∃ players_to_be_removed: List (Fin (N * (N + 1))),
  players_to_be_removed.length = N * (N - 1) ∧
  let newRow : List ℝ := eraseIdxs heights players_to_be_removed
  let newRowWithIdxs : List (ℕ × ℝ) := List.zip (List.range (2 * N)) newRow
  let rowWithIdxsSortedByHeight : List (ℕ × ℝ) := newRowWithIdxs.insertionSort (λ a b => a.2 < b.2)
  ∀ i : Fin n,
  (rowWithIdxsSortedByHeight.get! (2*i)).1 = (rowWithIdxsSortedByHeight.get! (2*i + 1)).1 + 1
  ∨ (rowWithIdxsSortedByHeight.get! (2*i)).1 = (rowWithIdxsSortedByHeight.get! (2*i + 1)).1 - 1 :=
  sorry
