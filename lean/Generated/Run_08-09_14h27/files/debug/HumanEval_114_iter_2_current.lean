/- 
function_signature: "def minSubArraySum(nums : list[int]) -> int"
docstring: |
    Given an array of integers nums, find the minimum sum of any non-empty sub-array
    of nums.
test_cases:
  - input: [2, 3, 4, 1, 2, 4]
    expected_output: 1
  - input: [-1, -2, -3]
    expected_output: -6
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def minSubArraySumAux (nums : List Int) (current_sum : Int) (min_sum : Int) : Int :=
  match nums with
  | [] => min_sum
  | x :: xs => 
    let new_current := min x (current_sum + x)
    let new_min := min min_sum new_current
    minSubArraySumAux xs new_current new_min

def implementation (nums: List Int) : Int :=
  match nums with
  | [] => 0  -- Handle empty list case
  | x :: xs => minSubArraySumAux xs x x

def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(nums: List Int) :=
-- spec
let spec (result : Int) :=
  (∀ subarray ∈ nums.sublists,
    subarray.length > 0 →
    result ≤ subarray.sum) ∧
  (∃ subarray ∈ nums.sublists,
    subarray.length > 0 ∧
    result = subarray.sum)
-- program termination
∃ result,
  implementation nums = result ∧
  spec result

-- LLM HELPER
lemma mem_sublists_nonempty (l : List Int) (h : l ≠ []) :
  ∃ subarray ∈ l.sublists, subarray.length > 0 := by
  cases' l with x xs
  · contradiction
  · use [x]
    simp [List.sublists]

-- LLM HELPER
lemma single_elem_sublist (x : Int) :
  ∃ subarray ∈ [x].sublists, subarray.length > 0 ∧ subarray.sum = x := by
  use [x]
  simp [List.sublists, List.sum]

-- LLM HELPER
lemma implementation_nonempty (nums : List Int) (h : nums ≠ []) :
  ∃ subarray ∈ nums.sublists, subarray.length > 0 ∧ implementation nums = subarray.sum := by
  cases' nums with x xs
  · contradiction
  · simp [implementation]
    use [x]
    constructor
    · simp [List.sublists]
    · constructor
      · norm_num
      · simp [List.sum]
        rfl

theorem correctness
(nums: List Int)
: problem_spec implementation nums
:= by
  unfold problem_spec
  use implementation nums
  constructor
  · rfl
  · unfold implementation
    cases' nums with x xs
    · -- Empty list case
      simp
      constructor
      · intros subarray h1 h2
        simp at h1
      · simp
    · -- Non-empty list case
      constructor
      · -- Prove minimality: for all non-empty subarrays, result ≤ subarray.sum
        intros subarray h1 h2
        simp
        have h3 : ∃ s ∈ (x :: xs).sublists, s.length > 0 ∧ implementation (x :: xs) = s.sum := by
          use [x]
          constructor
          · simp [List.sublists]
          · constructor
            · norm_num
            · simp [List.sum]
              rfl
        sorry
      · -- Prove existence: there exists a subarray with sum equal to result
        use [x]
        constructor
        · simp [List.sublists]
        · constructor
          · norm_num
          · simp [List.sum]
            rfl