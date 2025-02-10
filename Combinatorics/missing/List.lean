import Mathlib.Data.List.DropRight
import Mathlib.Tactic.ApplyFun
import Mathlib.Data.Fintype.BigOperators

universe u

namespace List

def dropWhileRight {α : Type u} (P : α → Bool) (l : List α) : List α :=
  l.reverse.dropWhile P |>.reverse

@[simp]
lemma dropWhileRight_nil {α : Type u} (P : α → Bool) : List.dropWhileRight P [] = [] := by
  simp [List.dropWhileRight]

lemma dropWhileRight_sublist {α : Type u} (P : α → Bool) (l : List α) :
    l.dropWhileRight P <+ l := by
  simpa [dropWhileRight] using List.Sublist.reverse (l.reverse.dropWhile_sublist P)

theorem dropWhileRight_getLast?_not {α : Type u} (P : α → Bool) (l : List α) :
  ∀ (x : α), (l.dropWhileRight P).getLast? = some x → ¬ P x := by
  rintro x hx
  unfold List.dropWhileRight at hx
  rw [List.getLast?_reverse] at hx
  have := List.head?_dropWhile_not P l.reverse
  rw [hx] at this
  simp only at this
  exact ne_true_of_eq_false this

theorem dropWhileRight_getLast_not
    {α : Type u} (P : α → Bool) (l : List α) (h : l.dropWhileRight P ≠ []) :
  ¬ P ((l.dropWhileRight P).getLast h) := by
  have := l.dropWhileRight_getLast?_not P
  rw [List.getLast?_eq_getLast _ h] at this
  apply this _ rfl

theorem dropWhileRight_append {α : Type u} (P : α → Bool) (l l' : List α) :
    List.dropWhileRight P (l ++ l') =
    if l'.dropWhileRight P |>.isEmpty
    then List.dropWhileRight P l
    else l ++ List.dropWhileRight P l' := by
  split_ifs with H
  · simp only [List.dropWhileRight, List.isEmpty_eq_true, List.reverse_eq_nil_iff,
    List.dropWhile_eq_nil_iff, List.mem_reverse, List.reverse_append, List.reverse_inj] at H ⊢
    rw [List.dropWhile_append, if_pos]
    simpa
  · simp only [List.dropWhileRight, List.isEmpty_eq_true, List.reverse_eq_nil_iff,
    List.dropWhile_eq_nil_iff, List.mem_reverse, not_forall, Classical.not_imp, Bool.not_eq_true,
    List.reverse_append, List.reverse_eq_append_iff, List.reverse_reverse] at H ⊢
    rw [List.dropWhile_append, if_neg]
    simp only [List.isEmpty_eq_true, List.dropWhile_eq_nil_iff, List.mem_reverse, not_forall,
      Classical.not_imp, Bool.not_eq_true]
    tauto

lemma dropWhile_length {α : Type u} (P : α → Bool) (l : List α) :
    (l.dropWhile P).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.dropWhile_cons]
    split_ifs with H
    · exact ih.trans (Nat.le_succ xs.length)
    · simp

lemma dropWhileRight_length {α : Type u} (P : α → Bool) (l : List α) :
    (l.dropWhileRight P).length ≤ l.length := by
  simp only [List.dropWhileRight, List.length_reverse]
  exact l.reverse.dropWhile_length P |>.trans (by simp)

lemma dropWhileRight_map {α β : Type u} (P : β → Bool)
    (f : α → β) (l : List α) :
    (l.dropWhileRight (P ∘ f)).map f = (l.map f).dropWhileRight P := by
  simp [dropWhileRight, ← dropWhile_map]

lemma dropWhile_eq_self_iff' {α : Type u} (P : α → Bool) (l : List α) :
    l.dropWhile P = l ↔ ∀ (h : l ≠ []), ¬ P (l.head h) := by
  cases l with
  | nil => simp
  | cons x xs =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.head_cons, Bool.not_eq_true,
      forall_const]
    constructor
    · intro h
      rw [List.dropWhile_cons] at h
      split_ifs at h with H
      · apply_fun List.length at h
        simp only [List.length_cons] at h
        have := xs.dropWhile_length P
        omega
      · simpa using H
    · intro h
      rw [List.dropWhile_cons_of_neg (by simpa using h)]

@[simp]
lemma dropWhileRight_eq_self_iff {α : Type u} (P : α → Bool) (l : List α):
    l.dropWhileRight P = l ↔ ∀ (h : l ≠ []), ¬ P (l.getLast h) := by
  simp only [List.dropWhileRight, List.reverse_eq_iff, ne_eq, Bool.not_eq_true]
  rw [List.dropWhile_eq_self_iff']
  simp

@[simp]
lemma dropWhileRight_eq_nil_iff {α : Type u} (P : α → Bool) (l : List α):
    l.dropWhileRight P = [] ↔ ∀ x ∈ l, P x := by
  simp only [List.dropWhileRight, List.reverse_eq_iff, List.reverse_nil, List.dropWhile_eq_nil_iff,
    List.mem_reverse]

def fillToLength {α : Type u} (l : List α) (n : ℕ) (x : α) : List α :=
  l ++ List.replicate (n - l.length) x

lemma length_fillToLength {α : Type u} (l : List α) (n : ℕ) (x : α) (h : l.length ≤ n) :
    (l.fillToLength n x).length = n := by
  simp only [fillToLength, length_append, length_replicate]
  omega


@[simp]
lemma dropWhileRight_eq_fillToLength {α : Type u} [DecidableEq α] (l : List α) (a : α) :
    (l.dropWhileRight (· = a)).fillToLength l.length a = l := by
  induction l with
  | nil => simp [fillToLength]
  | cons x xs ih =>
    simp only [dropWhileRight, reverse_cons, dropWhile_append, isEmpty_eq_true,
      dropWhile_eq_nil_iff, mem_reverse, length_cons] at ih ⊢
    split_ifs with H
    · simp only [decide_eq_true_eq, dropWhile_cons, dropWhile_nil] at H ⊢
      split_ifs with H'
      · simp only [fillToLength, reverse_nil, length_nil, Nat.sub_zero, replicate_succ, nil_append,
          cons.injEq] at H ⊢
        subst H'
        refine ⟨rfl, List.ext_getElem (by simp) fun n hn hn ↦ ?_⟩
        simp only [getElem_replicate, Eq.symm, getElem_mem, H]
      · simp only [fillToLength, reverse_cons, reverse_nil, nil_append, length_singleton,
        Nat.add_one_sub_one, singleton_append, cons.injEq, true_and]
        refine List.ext_getElem (by simp) fun n hn hn ↦ ?_
        simp [Eq.symm, H]
    · simp only [decide_eq_true_eq, not_forall, Classical.not_imp] at H
      simp only [fillToLength, length_reverse, reverse_append, reverse_cons, reverse_nil,
        nil_append, singleton_append, length_cons, Nat.reduceSubDiff, cons_append, cons.injEq,
        true_and] at ih ⊢
      rw [ih]

def splitWhileRememberingPosition {α : Type*} :
    List (Option α) → List Bool × List α
  | [] => ([], [])
  | .none::l =>
    let res := splitWhileRememberingPosition l
    (false :: res.1, res.2)
  | .some a::l =>
    let res := splitWhileRememberingPosition l
    (true :: res.1, a::res.2)

-- #eval splitWhileRememberingPosition [.none, .some 1, .none, .some 2]

def mergingWithPosition {α : Type*} : (List Bool × List α) → List (Option α)
| ([], []) => []
| (false::bs, x) => .none::mergingWithPosition (bs, x)
| (true::bs, x::xs) => .some x::mergingWithPosition (bs, xs)
| _ => []

-- #eval mergingWithPosition ([false, true, false, true], [1, 2])

@[simp]
lemma splitWhileRememberingPosition_nil {α : Type*} :
    splitWhileRememberingPosition ([] : List (Option α)) = ([], []) := by
  simp [splitWhileRememberingPosition]

lemma splitWhileRememberingPosition_none_cons {α : Type*} (l : List (Option α)) :
    splitWhileRememberingPosition (.none :: l)  =
    (false :: l.splitWhileRememberingPosition.1, l.splitWhileRememberingPosition.2) := by
  simp [splitWhileRememberingPosition]

lemma splitWhileRememberingPosition_some_cons {α : Type*} (a : α) (l : List (Option α)) :
    splitWhileRememberingPosition (.some a :: l)  =
    (true :: l.splitWhileRememberingPosition.1, a::l.splitWhileRememberingPosition.2) := by
  simp [splitWhileRememberingPosition]

lemma splitWhileRememberingPosition_fst_count_false_length_add_snd_length {α : Type*} (l : List (Option α)) :
    (l.splitWhileRememberingPosition.1.count false) +
    (l.splitWhileRememberingPosition.2).length = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases x with
    | none =>
      simp only [splitWhileRememberingPosition_none_cons, count_cons_self, length_cons, ← ih]
      omega
    | some x =>
      simp only [splitWhileRememberingPosition_some_cons, ne_eq, Bool.false_eq_true,
        not_false_eq_true, count_cons_of_ne, length_cons, ← ih]
      omega

lemma splitWhileRememberingPosition_fst_length {α : Type*} (l : List (Option α)) :
    l.splitWhileRememberingPosition.1.length = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases x with
    | none =>
      simp only [splitWhileRememberingPosition_none_cons, length_cons, ih]
    | some x =>
      simp only [splitWhileRememberingPosition_some_cons, length_cons, ih]

lemma splitWhileRememberingPosition_fst_count_length
    {α : Type*} [DecidableEq α] (l : List (Option α)) :
  l.splitWhileRememberingPosition.1.count false = l.count .none := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases x with
    | none =>
      simp only [splitWhileRememberingPosition_none_cons, length_cons, ih, count_cons_self]
    | some x =>
      simp [splitWhileRememberingPosition_some_cons, ih]

lemma splitWhileRememberingPosition_snd_count
    {α : Type*} [DecidableEq α] (l : List (Option α)) (a : α) :
    (l.splitWhileRememberingPosition.2).count a = l.count (.some a) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases x with
    | none =>
      simp only [splitWhileRememberingPosition_none_cons, ih, ne_eq, reduceCtorEq,
        not_false_eq_true, count_cons_of_ne]
    | some x =>
      simp only [splitWhileRememberingPosition_some_cons]
      by_cases h : a = x
      · subst h
        simp only [count_cons_self, ih]
      · rw [count_cons_of_ne h, ih, count_cons_of_ne]
        contrapose! h
        simpa using h

@[simp]
lemma mergingWithPosition_nil {α : Type*} (l : List α) :
    mergingWithPosition ([], l) = [] := by
  induction l with
  | nil =>
    simp [mergingWithPosition]
  | cons x xs ih =>
    simp [mergingWithPosition, ih]

lemma mergingWithPosition_false_cons {α : Type*} (bs : List Bool) (xs : List α) :
    mergingWithPosition (false::bs, xs) = .none::mergingWithPosition (bs, xs) := by
  simp [mergingWithPosition]

lemma mergingWithPosition_true_cons {α : Type*} (bs : List Bool) (x : α) (xs : List α) :
    mergingWithPosition (true::bs, x::xs) = .some x::mergingWithPosition (bs, xs) := by
  simp [mergingWithPosition]

lemma mergingWithPosition_true_nil {α : Type*} (bs : List Bool)  :
    mergingWithPosition (α := α) (true::bs, []) = [] := by
  simp [mergingWithPosition]

lemma mergingWithPosition_splitWhileRememberingPosition {α : Type*} (l : List (Option α)) :
    mergingWithPosition (splitWhileRememberingPosition l) = l := by
  induction l with
  | nil => simp only [splitWhileRememberingPosition, mergingWithPosition]
  | cons x l ih =>
    cases x with
    | none =>
      rw [splitWhileRememberingPosition_none_cons, mergingWithPosition_false_cons, ih]
    | some x =>
      rw [splitWhileRememberingPosition_some_cons, mergingWithPosition_true_cons, ih]

lemma splitWhileRememberingPosition_mergingWithPosition {α : Type*}
    (x : List Bool × List α) (hx : x.2.length = x.1.count true) :
    splitWhileRememberingPosition (mergingWithPosition x) = x := by
  cases x with | mk bs x =>
  induction bs generalizing x with
  | nil =>
    induction x with
    | nil => simp
    | cons x xs ih =>
      simp only [length_cons, count_nil, Nat.add_one_ne_zero] at hx
  | cons b bs ih =>
    simp only at ih hx ⊢
    cases b with
    | true =>
      simp only [count_cons_self] at hx ih ⊢
      obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_length_eq_add_one hx
      simp only [length_cons, Nat.add_right_cancel_iff] at hx
      specialize ih xs hx
      simp [ih, mergingWithPosition_true_cons, splitWhileRememberingPosition_some_cons]
    | false =>
      simp only [ne_eq, Bool.true_eq_false, not_false_eq_true, count_cons_of_ne] at hx ih ⊢
      specialize ih x hx
      simp [ih, mergingWithPosition_false_cons, splitWhileRememberingPosition_none_cons]

lemma mergingWithPosition_length {α : Type*} (x : List Bool × List α)
      (hx : x.2.length = x.1.count true) :
    (mergingWithPosition x).length = x.1.length := by
  induction x with | mk bs x =>
  induction bs generalizing x with
  | nil =>
    simp only [nodup_nil, count_nil, length_eq_zero] at hx
    subst hx
    simp
  | cons b bs ih =>
    cases b with
    | true =>
      simp only [count_cons_self, length_cons] at hx ih ⊢
      obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_length_eq_add_one hx
      simp only [length_cons, add_left_inj] at hx
      specialize ih xs hx
      rw [mergingWithPosition_true_cons, length_cons, ih]
    | false =>
      simp only [ne_eq, Bool.true_eq_false, not_false_eq_true, count_cons_of_ne,
        length_cons] at hx ih ⊢
      specialize ih x hx
      rw [mergingWithPosition_false_cons, length_cons, ih]

lemma mergingWithPosition_count_none {α : Type*} [DecidableEq α] (x : List Bool × List α)
      (hx : x.2.length = x.1.count true) :
    (mergingWithPosition x).count .none = x.1.count false := by
  induction x with | mk bs x =>
  induction bs generalizing x with
  | nil =>
    simp only [nodup_nil, count_nil, length_eq_zero] at hx
    subst hx
    simp
  | cons b bs ih =>
    cases b with
    | true =>
      simp only [count_cons_self, length_cons] at hx ih ⊢
      obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_length_eq_add_one hx
      simp only [length_cons, add_left_inj] at hx
      specialize ih xs hx
      rw [mergingWithPosition_true_cons, count_cons_of_ne, ih, count_cons_of_ne]
      <;> aesop
    | false =>
      simp only [ne_eq, Bool.true_eq_false, not_false_eq_true, count_cons_of_ne,
        length_cons] at hx ih ⊢
      specialize ih x hx
      rw [mergingWithPosition_false_cons, count_cons_self, ih, count_cons_self]

lemma mergingWithPosition_count_some {α : Type*} [DecidableEq α] (x : List Bool × List α)
      (hx : x.2.length = x.1.count true) (a : α) :
    (mergingWithPosition x).count (.some a) = x.2.count a := by
  induction x with | mk bs x =>
  induction bs generalizing x with
  | nil =>
    simp only [nodup_nil, count_nil, length_eq_zero] at hx
    subst hx
    simp
  | cons b bs ih =>
    cases b with
    | true =>
      simp only [count_cons_self, length_cons] at hx ih ⊢
      obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_length_eq_add_one hx
      simp only [length_cons, add_left_inj] at hx
      specialize ih xs hx
      by_cases h : a = x
      · subst h
        rw [mergingWithPosition_true_cons, count_cons_self, ih, count_cons_self]
      · rw [mergingWithPosition_true_cons, count_cons_of_ne (by aesop), ih, count_cons_of_ne h]
    | false =>
      simp only [ne_eq, Bool.true_eq_false, not_false_eq_true, count_cons_of_ne,
        length_cons] at hx ih ⊢
      specialize ih x hx
      rw [mergingWithPosition_false_cons, count_cons_of_ne (by aesop), ih]

lemma length_eq_sum_count {α : Type*} [Fintype α] [DecidableEq α] (l : List α) :
    l.length = ∑ (a : α), l.count a := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [length_cons]
    have (a : α) : count a (x :: xs) = if a = x then (count a xs) + 1 else count a xs := by
      split_ifs with H
      · subst H; simp
      · rw [count_cons_of_ne H]
    simp_rw [this]
    rw [ih, add_comm, show (1 : ℕ) = ∑ a : α, if a = x then 1 else 0 by
      simp, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    split_ifs with H <;> simp [H, add_comm]

lemma length_eq_sum_count' {α : Type*} [DecidableEq α] (l : List α) :
    l.length = ∑ a ∈ l.toFinset.filter (fun a ↦ l.count a ≠ 0), l.count a := by
  classical
  let L : List {x | x ∈ l} := l.attach
  rw [← l.length_attach, length_eq_sum_count]

  rw [← Finset.sum_subset (s₁ := Finset.univ.filter (fun (a : {x // x ∈ l}) ↦ l.count a.1 ≠ 0))]
  pick_goal 2
  · exact Finset.filter_subset _ _
  pick_goal 2
  · simp

  fapply Finset.sum_bij'
  · refine fun a ha ↦ a.1
  · refine fun a ha => ⟨a, by aesop⟩
  · simp [List.count_eq_zero]
  · simp
  · simp
  · simp
  · simp


end List
