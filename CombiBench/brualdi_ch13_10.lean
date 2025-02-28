import Mathlib


universe u

structure IsTournament {V : Type u} (G : Digraph V) : Prop where
  irrefl : ∀ (u : V), ¬ G.Adj u u
  adj : ∀ (u v : V), u ≠ v → G.Adj u v ∨ G.Adj v u

-- a walk is a sequence of edges such that the end of the `i`-th edge is the start of the `i+1`-th edge
inductive Digraph.Walk {V : Type u} (G : Digraph V) : V → V → Type u
  | nil {u : V} (h : G.Adj u u) : Digraph.Walk G u u
  | cons {u v w : V} (h : G.Adj u v) (p : Digraph.Walk G v w) : Digraph.Walk G u w
  deriving DecidableEq

-- a connected digraph is one such that for any distinct vertices `u` and `v`, there is a walk from
-- `u` to `v` or from `v` to `u`
structure Diagraph.Connected {V : Type u} (G : Digraph V) : Prop where
  exists_walk ⦃u v : V⦄ (neq : u ≠ v) : Nonempty (Digraph.Walk G u v) ∨ Nonempty (Digraph.Walk G v u)

-- a strongly connected digraph is one such that for any distinct vertices `u` and `v`, there is a
-- walk from `u` to `v` and from `v` to `u`. Note that since `u ≠ v ↔ v ≠ u`, we only need to assert
-- that there is a walk from `u` to `v`.
structure Digraph.StronglyConnected {V : Type u} (G : Digraph V) : Prop where
  exists_walk ⦃u v : V⦄ (neq : u ≠ v) : Nonempty (Digraph.Walk G u v)

-- the support of a walk is the list of vertices that the walk traverses in order.
def Digraph.Walk.support {V : Type u} {G : Digraph V} {u v : V} : Digraph.Walk G u v → List V
| .nil h => [u]
| .cons _ p => u :: p.support

-- a walk is a path if it does not visit the same vertex twice, hence a Hamilton cycle is a path
-- that starts and ends at the same vertex.
def Digraph.Walk.IsPath {V : Type u} {G : Digraph V} {u v : V} (p : Digraph.Walk G u v) : Prop :=
  p.support.Nodup

def Digraph.Walk.length {V : Type u} {G : Digraph V} {u v : V} : Digraph.Walk G u v → ℕ
| .nil h => 1
| .cons _ p => 1 + p.length

lemma Digraph.Walk.length_eq_support_length {V : Type u} {G : Digraph V} {u v : V} (p : Digraph.Walk G u v) :
  p.length = p.support.length := by
  induction p with
  | nil h => rfl
  | cons h p ih =>
    simp [Digraph.Walk.length, Digraph.Walk.support, ih, add_comm]

/--
Prove that every tournament contains a vertex $u$ such that, for every other vertex $x$, there is a path from $u$ to $x$ of length at most 2.
-/
theorem brualdi_ch13_10 {V : Type u} (T : Digraph V) (hT : IsTournament T) :
    ∃ (u : V), ∀ (x : V), ∃ (p : T.Walk u x), p.length ≤ 2 := by sorry
