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

noncomputable def implementation (l: List Int) : List Int :=
  l.toFinset.toList.mergeSort (fun x y => decide (x ≤ y))

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
  have : l.toFinset.toList.Nodup := by apply Finset.nodup_toList
  exact List.count_eq_one_of_mem this h

-- LLM HELPER
lemma int_le_trans (a b c : Int) : decide (a ≤ b) = true → decide (b ≤ c) = true → decide (a ≤ c) = true := by
  intro h1 h2
  simp at h1 h2
  simp
  exact le_trans h1 h2

-- LLM HELPER
lemma int_le_total (a b : Int) : (decide (a ≤ b) || decide (b ≤ a)) = true := by
  simp
  exact le_total a b

-- LLM HELPER
lemma int_le_equiv (a b : Int) : a.le b ↔ decide (a ≤ b) = true := by
  simp [Int.le]

-- LLM HELPER
lemma sorted_mergeSort (l: List Int) : List.Sorted Int.le (l.mergeSort (fun x y => decide (x ≤ y))) := by
  have h1 := List.sorted_mergeSort int_le_trans int_le_total l
  convert h1 using 1
  ext a b
  exact int_le_equiv a b

-- LLM HELPER
lemma mem_mergeSort_iff (l: List Int) (x: Int) : x ∈ l.mergeSort (fun x y => decide (x ≤ y)) ↔ x ∈ l := by
  exact List.mem_mergeSort

-- LLM HELPER  
lemma count_mergeSort_eq (l: List Int) (x: Int) : 
  List.Nodup l → (l.mergeSort (fun x y => decide (x ≤ y))).count x = l.count x := by
  intro h
  exact List.count_mergeSort_le h

theorem correctness
(l: List Int)
: problem_spec implementation l
:= by
  unfold problem_spec implementation
  use l.toFinset.toList.mergeSort (fun x y => decide (x ≤ y))
  constructor
  · rfl
  · constructor
    · intro x
      constructor
      · intro h
        have h1 : x ∈ l.toFinset.toList := by
          rw [mem_mergeSort_iff] at h
          exact h
        constructor
        · rw [← mem_toFinset_toList]
          exact h1
        · have h2 : x ∈ l.toFinset.toList := by
            rw [mem_mergeSort_iff] at h
            exact h
          rw [count_mergeSort_eq]
          · exact count_toFinset_toList l x h2
          · have : l.toFinset.toList.Nodup := by apply Finset.nodup_toList
            exact this
      · intro h
        rw [mem_mergeSort_iff]
        rw [mem_toFinset_toList]
        exact h.1
    · exact sorted_mergeSort (l.toFinset.toList)

-- #test implementation [5, 3, 5, 2, 3, 3, 9, 0, 123] = [0, 2, 3, 5, 9, 123]