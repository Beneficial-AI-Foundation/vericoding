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
      constructor
      · intro h_eq
        left
        exact h_eq
      · intro h_or
        cases h_or with
        | inl h_eq => exact h_eq
        | inr h_in => 
          rw [ih] at h_mem
          exact h_in
    · simp [h_mem, ih]
      constructor
      · intro h_or
        cases h_or with
        | inl h_eq => 
          left
          exact h_eq
        | inr h_in =>
          right
          exact h_in
      · intro h_or
        cases h_or with
        | inl h_eq =>
          left
          exact h_eq
        | inr h_in =>
          right
          exact h_in

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
      constructor
      · intro h_or
        cases h_or with
        | inl h_eq => 
          left
          exact h_eq
        | inr h_or2 =>
          cases h_or2 with
          | inl h_eq2 =>
            right
            left
            exact h_eq2
          | inr h_in =>
            right
            right
            exact h_in
      · intro h_or
        cases h_or with
        | inl h_eq =>
          left
          exact h_eq
        | inr h_or2 =>
          cases h_or2 with
          | inl h_eq2 =>
            right
            left
            exact h_eq2
          | inr h_in =>
            right
            right
            exact h_in

-- LLM HELPER
lemma mem_sortList (x: Int) (l: List Int) :
  x ∈ sortList l ↔ x ∈ l := by
  induction l with
  | nil => simp [sortList]
  | cons h t ih =>
    simp [sortList, mem_insertSorted, ih]

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
        cases t with
        | nil =>
          simp [insertSorted] at ih_result
          exact List.Sorted.cons (Int.le_of_not_le h_le) ih_result
        | cons t_h t_t =>
          simp [insertSorted] at ih_result
          by_cases h_le2 : x ≤ t_h
          · simp [h_le2] at ih_result
            exact List.Sorted.cons h_rel ih_result
          · simp [h_le2] at ih_result
            exact List.Sorted.cons h_rel ih_result
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
lemma count_sortList (x: Int) (l: List Int) :
  (sortList l).count x = l.count x := by
  induction l with
  | nil => simp [sortList]
  | cons h t ih =>
    simp [sortList]
    rw [List.count_cons]
    have count_insert : (insertSorted h (sortList t)).count x = 
      (if x = h then 1 else 0) + (sortList t).count x := by
      induction sortList t with
      | nil => 
        simp [insertSorted]
        rw [List.count_cons, List.count_nil]
      | cons sh st ih_inner =>
        simp [insertSorted]
        by_cases h_le : h ≤ sh
        · simp [h_le]
          rw [List.count_cons]
          simp
        · simp [h_le]
          rw [List.count_cons]
          by_cases h_eq : x = sh
          · simp [h_eq]
            have : (insertSorted h st).count sh = st.count sh := by
              induction st with
              | nil => 
                simp [insertSorted]
                by_cases h_eq2 : sh = h
                · simp [h_eq2]
                · simp [h_eq2]
              | cons sth stt ih_inner2 =>
                simp [insertSorted]
                by_cases h_le2 : h ≤ sth
                · simp [h_le2]
                  rw [List.count_cons]
                  by_cases h_eq3 : sh = h
                  · simp [h_eq3]
                  · simp [h_eq3]
                · simp [h_le2]
                  rw [List.count_cons]
                  by_cases h_eq4 : sh = sth
                  · simp [h_eq4]
                    exact ih_inner2
                  · simp [h_eq4]
                    exact ih_inner2
            rw [this]
          · simp [h_eq]
            exact ih_inner
    rw [count_insert, ih]

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