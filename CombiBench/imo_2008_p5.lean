import Mathlib

def turn_one (n : ℕ+) (i : Fin (2 * n)) (a : List Bool) : List Bool :=
  List.zipWith (fun x (y : Bool) => if x = i then ¬y else y) (List.ofFn (fun i : Fin (2 * n) => i)) a

def turn_state (n : ℕ+) (l : List (Fin (2 * n))) : List Bool :=
  match l with
  | [] => (List.ofFn (fun _ : Fin (2 * n) => false))
  | h :: t => turn_one n h (turn_state n t)

def final_goal (n : ℕ+) := List.ofFn (fun (i : Fin (2 * n)) => if i < n then true else false)

def N (n k : ℕ+) := @Finset.univ (Fin k → Fin (2 * n)) _ |>.filter
  (fun f => turn_state n (List.ofFn f) = final_goal n) |>.card

def M (n k : ℕ+) := @Finset.univ (Fin k → Fin (2 * n)) _ |>.filter
  (fun f => ∀ (i : Fin k), f i < (n : Fin (2 * n))) |>.filter
  (fun f => turn_state n (List.ofFn f) = final_goal n) |>.card

abbrev imo_2008_p5_solution (n k : ℕ+) : ℝ := sorry

/--
Let $n$ and $k$ be positive integers with $k \geq n$ and $k - n$ an even number. Let $2n$ lamps labelled $1$, $2$, ..., $2n$ be given, each of which can be either on or off. Initially all the lamps are off. We consider sequences of steps: at each step one of the lamps is switched (from on to off or from off to on). Let $N$ be the number of such sequences consisting of $k$ steps and resulting in the state where lamps $1$ through $n$ are all on, and lamps $n + 1$ through $2n$ are all off. Let $M$ be number of such sequences consisting of $k$ steps, resulting in the state where lamps $1$ through $n$ are all on, and lamps $n + 1$ through $2n$ are all off, but where none of the lamps $n + 1$ through $2n$ is ever switched on. Determine $\frac{N}{M}$.
-/
theorem imo_2008_p5 (n k : ℕ+) (hnk : k ≥ n) (hnk' : Even (k - n)) :
    N n k / M n k = imo_2008_p5_solution n k := by sorry
