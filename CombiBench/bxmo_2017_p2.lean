import Mathlib

variable (n : ℕ) (h_n : n ≥ 2)

-- Convention: We rename the islands such that the first factory is on island zero and the second factory is on island one.

abbrev GameState := SimpleGraph (Fin n)

def GameState.initial : GameState n := ⊥

structure Move where
  island1 : Fin n
  island2 : Fin n
  valid: island1 ≠ island2

def GameState.next {n : ℕ} (s : GameState n) (m : Move n) : GameState n :=
  s ⊔ SimpleGraph.fromRel λ i j => (i = m.island1 ∧ j = m.island2) ∨ (j = m.island1 ∧ i = m.island2)

def GameState.is_losing_state {n : ℕ} (h_n : n ≥ 2) (s : GameState n) : Prop :=
  Nonempty (s.Path ⟨0, by linarith [h_n]⟩ ⟨1, by linarith [h_n]⟩ )

abbrev Strategy := GameState n → Move n

instance (s: GameState n) : Decidable (GameState.is_losing_state h_n s) := sorry

partial def aliceWins (s : GameState n) (s1: Strategy n) (s2: Strategy n): Bool :=
  let state_after_player1 := s.next (s1 s);
  if state_after_player1.is_losing_state h_n then
    False
  else
    let state_after_player_2 := state_after_player1.next (s2 state_after_player1);
    if state_after_player_2.is_losing_state h_n then
      True
    else
      aliceWins state_after_player_2 s1 s2

def solution_set : Set ℕ := sorry

/-- 214
Let \\( n \\geqslant 2 \\) be an integer. Alice and Bob play a game concerning a country made of \\( n \\) islands. Exactly two of those \\( n \\) islands have a factory. Initially there is no bridge in the country. Alice and Bob take turns in the following way. In each turn, the player must build a bridge between two different islands \\( I_{1} \\) and \\( I_{2} \\) such that:

- \\( I_{1} \\) and \\( I_{2} \\) are not already connected by a bridge;
- at least one of the two islands \\( I_{1} \\) and \\( I_{2} \\) is connected by a series of bridges to an island with a factory (or has a factory itself). (Indeed, access to a factory is needed for the construction.)

As soon as a player builds a bridge that makes it possible to go from one factory to the other, this player loses the game. (Indeed, it triggers an industrial battle between both factories.) If Alice starts, then determine (for each \\( n \\geqslant 2 \\)) who has a winning strategy.

(Note: It is allowed to construct a bridge passing above another bridge.)
-/
theorem bxmo_2017_p2 : (n ∈ solution_set →
  ∃ strategyA , ∀ strategyB, aliceWins n h_n (GameState.initial n) strategyA strategyB)
  ∧ (n ∉ solution_set →
  ∃ strategyB, ∀ strategyA, ¬ aliceWins n h_n (GameState.initial n) strategyA strategyB)
  := by sorry
