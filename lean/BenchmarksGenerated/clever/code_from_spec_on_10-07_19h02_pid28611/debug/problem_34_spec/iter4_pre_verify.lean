import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(l: List Int) :=
-- spec
let spec (result: List Int) :=
  (∀ x, x ∈ result ↔ x ∈ l ∧ result.count x = 1) ∧
  List.Sorted Int.le result
-- program termination
∃ result,
  implementation l = result ∧
  spec result

-- LLM HELPER
def removeDuplicates (l: List Int) : List Int :=
  l.foldr (fun x acc => if x ∈ acc then acc else x :: acc) []

-- LLM HELPER
def insertSorted (x: Int) (l: List Int) : List Int :=
  match l with
  | [] => [x]
  | h :: t => if x ≤ h then x :: l else h :: insertSorted x t

-- LLM HELPER
def sortList (l: List Int) : List Int :=
  l.foldr insertSorted []

def implementation (l: List Int) : List Int := 
  sortList (removeDuplicates l)

-- LLM HELPER
lemma mem_removeDuplicates (x: Int) (l: List Int) : 
  x ∈ removeDuplicates l ↔ x ∈ l := by
  induction l with
  | nil => simp [removeDuplicates]
  | cons h t ih =>
    simp [removeDuplicates]
    by_cases h_mem : h ∈ removeDuplicates t
    · simp [h_mem, ih]
    · simp [h_mem, ih]

-- LLM HELPER
lemma count_removeDuplicates (x: Int) (l: List Int) :
  x ∈ removeDuplicates l → (removeDuplicates l).count x = 1 := by
  induction l with
  | nil => simp [removeDuplicates]
  | cons h t ih =>
    simp [removeDuplicates]
    by_cases h_mem : h ∈ removeDuplicates t
    · simp [h_mem]
      intro h_in
      exact ih h_in
    · simp [h_mem]
      intro h_or
      cases h_or with
      | inl h_eq =>
        simp [h_eq]
        rw [List.count_cons_self]
        simp [h_mem]
      | inr h_in =>
        have h_ne : x ≠ h := by
          intro h_eq_h
          rw [h_eq_h] at h_in
          rw [mem_removeDuplicates] at h_in
          exact h_mem h_in
        rw [List.count_cons_of_ne h_ne]
        exact ih h_in

-- LLM HELPER
lemma mem_insertSorted (x y: Int) (l: List Int) :
  x ∈ insertSorted y l ↔ x = y ∨ x ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons h t ih =>
    simp [insertSorted]
    by_cases h_le : y ≤ h
    · simp [h_le]
    · simp [h_le, ih]

-- LLM HELPER
lemma mem_sortList (x: Int) (l: List Int) :
  x ∈ sortList l ↔ x ∈ l := by
  induction l with
  | nil => simp [sortList]
  | cons h t ih =>
    simp [sortList]
    rw [mem_insertSorted, ih]

-- LLM HELPER
lemma sorted_insertSorted (x: Int) (l: List Int) :
  List.Sorted Int.le l → List.Sorted Int.le (insertSorted x l) := by
  intro h_sorted
  induction l with
  | nil => 
    simp [insertSorted]
    exact List.sorted_singleton
  | cons h t ih =>
    simp [insertSorted]
    by_cases h_le : x ≤ h
    · simp [h_le]
      exact List.Sorted.cons h_le h_sorted
    · simp [h_le]
      cases h_sorted with
      | cons h_rel h_sorted_t =>
        have ih_result := ih h_sorted_t
        have h_le_x : h ≤ x := Int.le_of_not_le h_le
        suffices h_all : ∀ a ∈ insertSorted x t, h ≤ a
        from List.Sorted.cons h_all ih_result
        intro a ha
        rw [mem_insertSorted] at ha
        cases ha with
        | inl h_eq => 
          simp [h_eq]
          exact h_le_x
        | inr h_in => 
          exact h_rel a h_in
      | nil =>
        simp [insertSorted]
        exact List.Sorted.cons (Int.le_of_not_le h_le) List.sorted_nil

-- LLM HELPER
lemma sorted_sortList (l: List Int) :
  List.Sorted Int.le (sortList l) := by
  induction l with
  | nil => 
    simp [sortList]
    exact List.sorted_nil
  | cons h t ih =>
    simp [sortList]
    exact sorted_insertSorted h (sortList t) ih

-- LLM HELPER
lemma count_insertSorted (x y: Int) (l: List Int) :
  (insertSorted y l).count x = l.count x + (if x = y then 1 else 0) := by
  induction l with
  | nil => 
    simp [insertSorted]
    by_cases h : x = y
    · simp [h]
    · simp [h]
  | cons h t ih =>
    simp [insertSorted]
    by_cases h_le : y ≤ h
    · simp [h_le]
      rw [List.count_cons, List.count_cons]
      by_cases h_eq : x = y
      · simp [h_eq]
        ring
      · simp [h_eq]
        by_cases h_eq2 : x = h
        · simp [h_eq2]
          have h_ne : ¬y = h := by
            intro h_eq_h
            rw [h_eq_h] at h_le
            rw [h_eq2] at h_le
            rw [h_eq2] at h_eq
            exact h_eq rfl
          simp [h_ne]
        · simp [h_eq2]
    · simp [h_le]
      rw [List.count_cons, List.count_cons, ih]
      by_cases h_eq : x = h
      · simp [h_eq]
        ring
      · simp [h_eq]
        ring

-- LLM HELPER
lemma count_sortList (x: Int) (l: List Int) :
  (sortList l).count x = l.count x := by
  induction l with
  | nil => simp [sortList]
  | cons h t ih =>
    simp [sortList]
    rw [count_insertSorted, ih]
    rw [List.count_cons]
    ring

theorem correctness
(l: List Int)
: problem_spec implementation l := by
  simp [problem_spec, implementation]
  use sortList (removeDuplicates l)
  constructor
  · rfl
  · constructor
    · intro x
      constructor
      · intro h_in
        rw [mem_sortList, mem_removeDuplicates] at h_in
        constructor
        · exact h_in
        · rw [count_sortList]
          exact count_removeDuplicates x l (by rw [mem_removeDuplicates]; exact h_in)
      · intro ⟨h_in, h_count⟩
        rw [mem_sortList, mem_removeDuplicates]
        exact h_in
    · exact sorted_sortList (removeDuplicates l)