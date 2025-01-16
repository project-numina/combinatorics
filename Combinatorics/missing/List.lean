import Mathlib.Data.List.Basic
import Mathlib.Tactic.ApplyFun

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

lemma dropWhile_eq_self_iff {α : Type u} (P : α → Bool) (l : List α) :
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
  rw [List.dropWhile_eq_self_iff]
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

end List
