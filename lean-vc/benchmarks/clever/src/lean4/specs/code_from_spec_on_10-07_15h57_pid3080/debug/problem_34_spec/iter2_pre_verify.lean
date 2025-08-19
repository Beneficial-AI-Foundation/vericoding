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

def implementation (l: List Int) : List Int := (l.dedup).mergeSort Int.le

-- LLM HELPER
lemma mem_dedup_iff {α : Type*} [DecidableEq α] (a : α) (l : List α) :
  a ∈ l.dedup ↔ a ∈ l := by
  induction l with
  | nil => simp [List.dedup]
  | cons h t ih =>
    simp [List.dedup]
    split_ifs with h_in
    · simp [List.mem_cons]
      rw [ih]
      constructor
      · intro h_mem
        exact Or.inr h_mem
      · intro h_mem
        cases h_mem with
        | inl h_eq => 
          rw [← h_eq]
          exact h_in
        | inr h_mem_t => exact h_mem_t
    · simp [List.mem_cons]
      rw [ih]

-- LLM HELPER
lemma count_dedup_eq_one {α : Type*} [DecidableEq α] (a : α) (l : List α) :
  a ∈ l.dedup → l.dedup.count a = 1 := by
  induction l with
  | nil => simp [List.dedup]
  | cons h t ih =>
    simp [List.dedup]
    split_ifs with h_in
    · intro h_mem
      rw [ih h_mem]
    · intro h_mem
      simp [List.count_cons]
      cases h_mem with
      | inl h_eq =>
        rw [← h_eq]
        simp
        have : a ∉ t.dedup := by
          rw [mem_dedup_iff]
          exact h_in
        rw [List.count_eq_zero_of_not_mem this]
      | inr h_mem_t =>
        simp
        have : a ≠ h := by
          intro h_eq
          rw [h_eq] at h_mem_t
          have : h ∈ t.dedup := h_mem_t
          rw [mem_dedup_iff] at this
          exact h_in this
        simp [this]
        exact ih h_mem_t

-- LLM HELPER
lemma sorted_mergeSort (l : List Int) :
  List.Sorted Int.le (l.mergeSort Int.le) := by
  apply List.sorted_mergeSort
  exact Int.le_total

-- LLM HELPER
lemma mem_mergeSort_iff (a : Int) (l : List Int) :
  a ∈ l.mergeSort Int.le ↔ a ∈ l := by
  constructor
  · intro h
    exact List.mem_of_mem_mergeSort h
  · intro h
    exact List.mem_mergeSort_of_mem h

-- LLM HELPER
lemma count_mergeSort (a : Int) (l : List Int) :
  (l.mergeSort Int.le).count a = l.count a := by
  apply List.count_mergeSort
  exact Int.le_total

theorem correctness
(l: List Int)
: problem_spec implementation l
:= by
  unfold problem_spec implementation
  use (l.dedup).mergeSort Int.le
  constructor
  · rfl
  · constructor
    · intro x
      constructor
      · intro h
        constructor
        · rw [mem_mergeSort_iff] at h
          rw [mem_dedup_iff] at h
          exact h
        · rw [count_mergeSort]
          apply count_dedup_eq_one
          rw [← mem_mergeSort_iff]
          exact h
      · intro ⟨h1, h2⟩
        rw [mem_mergeSort_iff]
        rw [mem_dedup_iff]
        exact h1
    · exact sorted_mergeSort (l.dedup)