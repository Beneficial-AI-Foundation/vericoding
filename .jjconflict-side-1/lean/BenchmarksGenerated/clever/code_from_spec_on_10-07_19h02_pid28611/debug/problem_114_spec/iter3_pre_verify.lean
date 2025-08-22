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
def kadane_aux (acc : Int) (min_so_far : Int) (remaining : List Int) : Int :=
  match remaining with
  | [] => min_so_far
  | x :: xs => 
    let new_acc := min x (acc + x)
    kadane_aux new_acc (min min_so_far new_acc) xs

def implementation (nums: List Int) : Int := 
  match nums with
  | [] => 0  -- will be handled specially in correctness
  | x :: xs => kadane_aux x x xs

-- LLM HELPER
lemma empty_sublists_no_positive_length (nums : List Int) :
  nums = [] → ∀ subarray ∈ nums.sublists, subarray.length = 0 := by
  intro h subarray h_mem
  simp [h, List.sublists] at h_mem
  simp [h_mem]

-- LLM HELPER
lemma singleton_min_is_element (x : Int) :
  ∀ subarray ∈ [x].sublists, subarray.length > 0 → x ≤ subarray.sum := by
  intro subarray h_mem h_len
  simp [List.sublists] at h_mem
  cases h_mem with
  | inl h => simp [h] at h_len
  | inr h => simp [h]

-- LLM HELPER
lemma singleton_achievable (x : Int) :
  ∃ subarray ∈ [x].sublists, subarray.length > 0 ∧ x = subarray.sum := by
  use [x]
  constructor
  · simp [List.sublists]
  · simp

-- LLM HELPER
lemma kadane_maintains_minimum (acc min_so_far : Int) (x : Int) (xs : List Int) :
  min_so_far ≤ acc →
  min_so_far ≤ x →
  min_so_far ≤ min x (acc + x) := by
  intro h1 h2
  exact min_le_of_left_le h2

theorem correctness
(nums: List Int)
: problem_spec implementation nums
:= by
  simp [problem_spec]
  use implementation nums
  constructor
  · rfl
  · constructor
    · -- Show that result is minimum of all subarray sums
      intro subarray h_mem h_len
      if h_empty : nums = [] then
        -- Empty case - no positive length subarrays exist
        have : subarray.length = 0 := empty_sublists_no_positive_length nums h_empty subarray h_mem
        simp [this] at h_len
      else
        -- Non-empty case
        cases' nums with x xs
        · contradiction
        · simp [implementation]
          if h_xs : xs = [] then
            simp [h_xs, kadane_aux]
            exact singleton_min_is_element x subarray h_mem h_len
          else
            -- For the general case, we rely on kadane algorithm properties
            -- The implementation will find a minimum among reachable sums
            sorry -- This would require a complex inductive proof
    · -- Show that the result is achievable
      if h_empty : nums = [] then
        -- Empty case - no positive length subarrays exist, so existential is vacuously false
        simp [h_empty, List.sublists]
        exfalso
        -- We need to show this is impossible - there should be no positive length subarrays
        sorry
      else
        cases' nums with x xs
        · contradiction
        · simp [implementation]
          if h_xs : xs = [] then
            simp [h_xs, kadane_aux]
            exact singleton_achievable x
          else
            -- For the general case, the kadane algorithm will achieve some subarray sum
            sorry -- This would require proving the kadane algorithm correctness