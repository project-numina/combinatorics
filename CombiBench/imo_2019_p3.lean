import Mathlib

variable (users :  SimpleGraph (Fin 2019))
noncomputable instance : Fintype (users.neighborSet a) := Fintype.ofFinite ↑(users.neighborSet a)

/-
a triple of distinct users a, b, c such that a is friends with b and c, but b and c are not friends.
-/
structure triple where
  (a b c : Fin 2019)
  (hab : users.Adj a b)
  (hac : users.Adj a c)
  (hbc : ¬ users.Adj b c)
  (hbc' : b ≠ c)

@[simp]
lemma triple.hab' (t : triple users) : t.b = t.c ↔ False := by
  constructor
  · exact (t.hbc' ·)
  · tauto

attribute [local aesop safe] SimpleGraph.Adj.symm triple.hbc'
/--
For any such triple of users a, b, c,
b and c becomes friends now, but a is no longer friends with b, and no longer friends with c.
-/
def update (t : triple users) :
  SimpleGraph (Fin 2019) where
    Adj x y :=
      if x = t.a then
        if y = t.b then False
        else if y = t.c then False
        else users.Adj t.a y
      else if x = t.b then
        if y = t.a then False
        else if y = t.c then True
        else users.Adj t.b y
      else if x = t.c then
        if y = t.a then False
        else if y = t.b then True
        else users.Adj t.c y
      else users.Adj x y
    symm := by
      simp only [if_false_left, if_true_left]
      intro x y
      simp only
      split_ifs <;> aesop
    loopless := by
      intro x
      simp only [if_false_left, if_true_left, SimpleGraph.irrefl, if_false_right]
      split_ifs with h1 h2 <;> try aesop

/--
The question is asking to prove that there exists a sequence of such events after which each user is friends with at most one other user.
So suppose the sequence has length (n + 1)

(note that the sequence can not have length 0, because the initial state does not satisfy the condition)
-/
def imo_2019_p3_solutionSeq_length
  (cond : ∃ (A B : Finset (Fin 2019)),
    A.card = 1010 ∧ B.card = 1009 ∧
    (∀ a ∈ A, (users.neighborFinset a).card = 1009) ∧
    (∀ b ∈ B, (users.neighborFinset b).card = 1010)) : ℕ := sorry

/--
Then a sequence is like this
-- 0 : U₀ : users,     T₀ : a triple of U₀
-- 1 : U₁ : update T₀, T₁ : a triple of U₁
-- 2 : U₂ : update T₁, T₂ : a triple of U₂
-- ...
-/
def seq (cond) : (Fin (imo_2019_p3_solutionSeq_length users cond + 1)) → Σ (u : SimpleGraph (Fin 2019)), triple u
| ⟨0, _⟩ => ⟨users, sorry⟩
| ⟨n+1, h⟩ => ⟨update (seq cond ⟨n, lt_trans (by omega) h⟩).1 (seq cond ⟨n, lt_trans (by omega) h⟩).2, sorry⟩

-- At the end of the sequence, each user is friends with at most one other user.
/--
A social network has $2019$ users, some pairs of whom are friends. Whenever user $A$ is friends with user $B$, user $B$ is also friends with user $A$. Events of the following kind may happen repeatedly, one at a time: Three users $A$, $B$, and $C$ such that $A$ is friends with both $B$ and $C$, but $B$ and $C$ are not friends, change their friendship statuses such that $B$ and $C$ are now friends, but $A$ is no longer friends with $B$, and no longer friends with $C$. All other friendship statuses are unchanged. Initially, $1010$ users have $1009$ friends each, and $1009$ users have $1010$ friends each. Prove that there exists a sequence of such events after which each user is friends with at most one other user.
-/
theorem imo_2019_p3
  (cond : ∃ (A B : Finset (Fin 2019)),
    A.card = 1010 ∧ B.card = 1009 ∧
    (∀ a ∈ A, (users.neighborFinset a).card = 1009) ∧
    (∀ b ∈ B, (users.neighborFinset b).card = 1010)) :
  ∀ i : Fin 2019,
      (seq _ cond (Fin.last _) |>.1.neighborFinset i).card ≤ 1 := by sorry
