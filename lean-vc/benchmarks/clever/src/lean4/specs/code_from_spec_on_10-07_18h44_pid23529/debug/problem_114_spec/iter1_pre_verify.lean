import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
def maxSubarraySum (nums: List Int) : Int :=
  match nums with
  | [] => 0
  | h :: t => 
    let rec helper (lst: List Int) (maxSoFar: Int) (maxEndingHere: Int) : Int :=
      match lst with
      | [] => maxSoFar
      | x :: xs => 
        let newMaxEndingHere := max x (maxEndingHere + x)
        let newMaxSoFar := max maxSoFar newMaxEndingHere
        helper xs newMaxSoFar newMaxEndingHere
    helper t h h

def implementation (nums: List Int) : Int := 
  match nums with
  | [] => 0
  | _ => maxSubarraySum nums

-- LLM HELPER
lemma sublists_nonempty_exists (nums: List Int) (h: nums ≠ []) : 
  ∃ subarray ∈ nums.sublists, subarray.length > 0 := by
  cases' nums with head tail
  · contradiction
  · use [head]
    constructor
    · simp [List.sublists]
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      simp [List.sublists]
    · simp

-- LLM HELPER
lemma maxSubarraySum_is_maximum (nums: List Int) (h: nums ≠ []) :
  ∀ subarray ∈ nums.sublists, subarray.length > 0 → maxSubarraySum nums ≤ subarray.sum := by
  sorry

-- LLM HELPER
lemma maxSubarraySum_is_achievable (nums: List Int) (h: nums ≠ []) :
  ∃ subarray ∈ nums.sublists, subarray.length > 0 ∧ maxSubarraySum nums = subarray.sum := by
  sorry

-- LLM HELPER
lemma empty_case (nums: List Int) (h: nums = []) :
  (∀ subarray ∈ nums.sublists, subarray.length > 0 → (0 : Int) ≤ subarray.sum) ∧
  (∃ subarray ∈ nums.sublists, subarray.length > 0 ∧ (0 : Int) = subarray.sum) := by
  constructor
  · intro subarray hm hlen
    simp [h] at hm
  · simp [h]

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  unfold problem_spec
  use implementation nums
  constructor
  · rfl
  · unfold implementation
    cases' h : nums with head tail
    · simp [h]
      apply empty_case
      exact h
    · simp [h]
      constructor
      · apply maxSubarraySum_is_maximum
        simp [h]
      · apply maxSubarraySum_is_achievable
        simp [h]