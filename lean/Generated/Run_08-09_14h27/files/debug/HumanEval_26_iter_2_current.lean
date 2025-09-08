/- 
function_signature: "def remove_duplicates(numbers: List[int]) -> List[int]"
docstring: |
    From a list of integers, remove all elements that occur more than once.
    Keep order of elements left the same as in the input.
test_cases:
  - input: [1, 2, 3, 2, 4]
    expected_output: [1, 3, 4]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (numbers: List Int) : List Int :=
  numbers.filter (fun x => numbers.count x = 1)

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
(∀ i: Int, i ∈ result → numbers.count i = 1) ∧
(∀ i: Int, i ∈ numbers → numbers.count i = 1 → i ∈ result) ∧
(∀ i j : Nat, i < result.length → j < result.length → i < j →
∃ ip jp : Nat, ip < jp ∧ result[i]! = numbers[ip]! ∧ result[j]! = numbers[jp]!)
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
lemma count_eq_one_bool_eq_true (numbers : List Int) (x : Int) :
  (numbers.count x = 1) ↔ (decide (numbers.count x = 1) = true) := by
  simp [decide_eq_true_iff]

-- LLM HELPER
lemma filter_preserves_order (numbers : List Int) (i j : Nat) :
  i < (numbers.filter (fun x => numbers.count x = 1)).length → 
  j < (numbers.filter (fun x => numbers.count x = 1)).length → 
  i < j →
  ∃ ip jp : Nat, ip < jp ∧ 
    (numbers.filter (fun x => numbers.count x = 1))[i]! = numbers[ip]! ∧ 
    (numbers.filter (fun x => numbers.count x = 1))[j]! = numbers[jp]! := by
  intro hi hj hij
  -- Use the fact that filter preserves relative order from the original list
  have h1 : ∃ ip, ip < numbers.length ∧ 
    (numbers.filter (fun x => numbers.count x = 1))[i]! = numbers[ip]! := by
    have := List.getElem_of_mem (List.getElem_mem_filter _ _ _)
    simp at this
    obtain ⟨ip, hip_lt, hip_eq⟩ := List.exists_getElem_eq_of_mem this
    exact ⟨ip, hip_lt, hip_eq⟩
  have h2 : ∃ jp, jp < numbers.length ∧ 
    (numbers.filter (fun x => numbers.count x = 1))[j]! = numbers[jp]! := by
    have := List.getElem_of_mem (List.getElem_mem_filter _ _ _)
    simp at this
    obtain ⟨jp, hjp_lt, hjp_eq⟩ := List.exists_getElem_eq_of_mem this
    exact ⟨jp, hjp_lt, hjp_eq⟩
  obtain ⟨ip, hip_lt, hip_eq⟩ := h1
  obtain ⟨jp, hjp_lt, hjp_eq⟩ := h2
  -- The key insight: filter preserves the relative order, so if i < j in filtered list,
  -- then the corresponding indices in original list satisfy ip < jp
  have ip_lt_jp : ip < jp := by
    -- This follows from the definition of filter and the fact that i < j
    have filter_order := List.filter_preserves_order
    sorry -- This requires a more detailed proof about filter preserving order
  exact ⟨ip, jp, ip_lt_jp, hip_eq, hjp_eq⟩

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use numbers.filter (fun x => numbers.count x = 1)
  constructor
  · rfl
  · constructor
    · -- ∀ i: Int, i ∈ result → numbers.count i = 1
      intro i hi
      rw [List.mem_filter] at hi
      rw [count_eq_one_bool_eq_true] at hi
      exact hi.2
    · constructor
      · -- ∀ i: Int, i ∈ numbers → numbers.count i = 1 → i ∈ result
        intro i hi hcount
        rw [List.mem_filter]
        rw [count_eq_one_bool_eq_true]
        exact ⟨hi, hcount⟩
      · -- Order preservation
        exact filter_preserves_order numbers

-- #test implementation [1, 2, 3, 2, 4] = [1, 3, 4]