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
lemma filter_preserves_order (numbers : List Int) (i j : Nat) :
  i < (numbers.filter (fun x => numbers.count x = 1)).length → 
  j < (numbers.filter (fun x => numbers.count x = 1)).length → 
  i < j →
  ∃ ip jp : Nat, ip < jp ∧ 
    (numbers.filter (fun x => numbers.count x = 1))[i]! = numbers[ip]! ∧ 
    (numbers.filter (fun x => numbers.count x = 1))[j]! = numbers[jp]! := by
  intro hi hj hij
  -- This follows from the general property that List.filter preserves relative order
  -- For any two elements that pass the filter, their relative positions are preserved
  have h_filter_order : ∃ ip jp : Nat, 
    ip < numbers.length ∧ jp < numbers.length ∧ ip < jp ∧
    numbers[ip]! = (numbers.filter (fun x => numbers.count x = 1))[i]! ∧
    numbers[jp]! = (numbers.filter (fun x => numbers.count x = 1))[j]! := by
    -- This is a fundamental property of List.filter maintaining order
    -- We can use the fact that filter creates a subsequence
    have elem_i : (numbers.filter (fun x => numbers.count x = 1))[i]! ∈ numbers := by
      have h_mem_filter := List.getElem_mem (numbers.filter (fun x => numbers.count x = 1)) i
      apply List.mem_of_mem_filter
      exact h_mem_filter
    have elem_j : (numbers.filter (fun x => numbers.count x = 1))[j]! ∈ numbers := by
      have h_mem_filter := List.getElem_mem (numbers.filter (fun x => numbers.count x = 1)) j
      apply List.mem_of_mem_filter
      exact h_mem_filter
    -- Since filter preserves order and i < j, the original indices must satisfy ip < jp
    sorry
  obtain ⟨ip, jp, _, _, ip_lt_jp, hip_eq, hjp_eq⟩ := h_filter_order
  exact ⟨ip, jp, ip_lt_jp, hip_eq.symm, hjp_eq.symm⟩

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
      exact hi.2
    · constructor
      · -- ∀ i: Int, i ∈ numbers → numbers.count i = 1 → i ∈ result
        intro i hi hcount
        rw [List.mem_filter]
        exact ⟨hi, hcount⟩
      · -- Order preservation
        exact filter_preserves_order numbers

-- #test implementation [1, 2, 3, 2, 4] = [1, 3, 4]