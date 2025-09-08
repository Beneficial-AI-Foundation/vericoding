/- 
function_signature: "def unique(l: list)"
docstring: |
    Return sorted unique elements in a list.
test_cases:
  - input: [5, 3, 5, 2, 3, 3, 9, 0, 123]
    output: [0, 2, 3, 5, 9, 123]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (l: List Int) : List Int :=
  l.toFinset.toList.mergeSort Int.le

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
lemma mem_toFinset_toList (l: List Int) (x: Int) : x ∈ l.toFinset.toList ↔ x ∈ l := by
  simp [List.mem_toFinset]

-- LLM HELPER
lemma count_toFinset_toList (l: List Int) (x: Int) : 
  x ∈ l.toFinset.toList → l.toFinset.toList.count x = 1 := by
  intro h
  simp [List.count_eq_one_of_mem h, Finset.nodup_toList]

-- LLM HELPER
lemma sorted_mergeSort (l: List Int) : List.Sorted Int.le (l.mergeSort Int.le) := by
  apply List.sorted_mergeSort
  exact Int.le_total

theorem correctness
(l: List Int)
: problem_spec implementation l
:= by
  unfold problem_spec implementation
  use l.toFinset.toList.mergeSort Int.le
  constructor
  · rfl
  · constructor
    · intro x
      constructor
      · intro h
        have h1 : x ∈ l.toFinset.toList := by
          rw [List.mem_mergeSort] at h
          exact h
        constructor
        · rw [← mem_toFinset_toList]
          exact h1
        · have h2 : x ∈ l.toFinset.toList := by
            rw [List.mem_mergeSort] at h
            exact h
          rw [List.count_mergeSort]
          exact count_toFinset_toList l x h2
      · intro h
        rw [List.mem_mergeSort]
        rw [mem_toFinset_toList]
        exact h.1
    · exact sorted_mergeSort (l.toFinset.toList)

-- #test implementation [5, 3, 5, 2, 3, 3, 9, 0, 123] = [0, 2, 3, 5, 9, 123]