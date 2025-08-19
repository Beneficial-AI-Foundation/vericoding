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
  exact List.mem_dedup

-- LLM HELPER
lemma count_dedup_eq_one {α : Type*} [DecidableEq α] (a : α) (l : List α) :
  a ∈ l.dedup → l.dedup.count a = 1 := by
  exact List.count_dedup

-- LLM HELPER
lemma sorted_mergeSort {α : Type*} [LinearOrder α] (l : List α) :
  List.Sorted (· ≤ ·) (l.mergeSort (· ≤ ·)) := by
  exact List.sorted_mergeSort (· ≤ ·) l

-- LLM HELPER
lemma mem_mergeSort_iff {α : Type*} [LinearOrder α] (a : α) (l : List α) :
  a ∈ l.mergeSort (· ≤ ·) ↔ a ∈ l := by
  exact List.mem_mergeSort (· ≤ ·) l

-- LLM HELPER
lemma count_mergeSort {α : Type*} [LinearOrder α] (a : α) (l : List α) :
  (l.mergeSort (· ≤ ·)).count a = l.count a := by
  exact List.count_mergeSort (· ≤ ·) l

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