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
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

def implementation (l: List Int) : List Int := 
  (removeDuplicates l).mergeSort Int.le

-- LLM HELPER
lemma mem_removeDuplicates (x : Int) (l : List Int) : 
  x ∈ removeDuplicates l ↔ x ∈ l := by
  simp [removeDuplicates]
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [List.foldl_cons]
    by_cases h_mem : h ∈ removeDuplicates t
    · simp [h_mem]
      rw [ih]
      tauto
    · simp [h_mem]
      rw [List.mem_append, List.mem_singleton]
      rw [ih]
      tauto

-- LLM HELPER
lemma count_removeDuplicates (x : Int) (l : List Int) :
  x ∈ removeDuplicates l → (removeDuplicates l).count x = 1 := by
  intro h
  simp [removeDuplicates] at h ⊢
  induction l with
  | nil => simp at h
  | cons head tail ih =>
    simp [List.foldl_cons]
    by_cases h_mem : head ∈ removeDuplicates tail
    · simp [h_mem]
      exact ih h
    · simp [h_mem]
      rw [List.count_append, List.count_singleton]
      by_cases h_eq : x = head
      · simp [h_eq]
        rw [mem_removeDuplicates] at h_mem
        simp [h_eq] at h_mem
        have : x ∉ removeDuplicates tail := by
          rw [mem_removeDuplicates]
          exact h_mem
        simp [List.count_eq_zero_of_not_mem this]
      · simp [h_eq]
        rw [List.mem_append, List.mem_singleton] at h
        cases h with
        | inl h_left => exact ih h_left
        | inr h_right => contradiction

-- LLM HELPER
lemma sorted_mergeSort (l : List Int) : List.Sorted Int.le (l.mergeSort Int.le) := by
  exact List.sorted_mergeSort Int.le l

-- LLM HELPER
lemma mem_mergeSort (x : Int) (l : List Int) : x ∈ l.mergeSort Int.le ↔ x ∈ l := by
  exact List.mem_mergeSort Int.le x l

-- LLM HELPER
lemma count_mergeSort (x : Int) (l : List Int) : (l.mergeSort Int.le).count x = l.count x := by
  exact List.count_mergeSort Int.le x l

theorem correctness
(l: List Int)
: problem_spec implementation l
:= by
  unfold problem_spec implementation
  use (removeDuplicates l).mergeSort Int.le
  constructor
  · rfl
  · constructor
    · intro x
      constructor
      · intro h
        rw [mem_mergeSort] at h
        rw [mem_removeDuplicates] at h
        constructor
        · exact h
        · rw [count_mergeSort]
          exact count_removeDuplicates x l (by rwa [←mem_removeDuplicates])
      · intro ⟨h1, h2⟩
        rw [mem_mergeSort, mem_removeDuplicates]
        exact h1
    · exact sorted_mergeSort (removeDuplicates l)