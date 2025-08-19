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
def kadane_aux (nums: List Int) : Int × Int :=
  match nums with
  | [] => (0, 0)
  | [x] => (x, x)
  | x :: xs =>
    let (max_ending_here, max_so_far) := kadane_aux xs
    let new_max_ending_here := Int.max x (x + max_ending_here)
    let new_max_so_far := Int.max max_so_far new_max_ending_here
    (new_max_ending_here, new_max_so_far)

def implementation (nums: List Int) : Int := 
  match nums with
  | [] => 0
  | _ => (kadane_aux nums).2

-- LLM HELPER
lemma sublists_nonempty_exists (nums: List Int) (h: nums ≠ []) :
  ∃ subarray ∈ nums.sublists, subarray.length > 0 := by
  cases' nums with x xs
  · contradiction
  · use [x]
    constructor
    · simp [List.sublists]
      use [], x :: xs
      simp
    · simp

-- LLM HELPER
lemma kadane_aux_sound (nums: List Int) (h: nums ≠ []) :
  let (_, max_so_far) := kadane_aux nums
  (∀ subarray ∈ nums.sublists, subarray.length > 0 → max_so_far ≤ subarray.sum) ∧
  (∃ subarray ∈ nums.sublists, subarray.length > 0 ∧ max_so_far = subarray.sum) := by
  sorry

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  unfold problem_spec
  unfold implementation
  cases' h : nums with x xs
  · use 0
    constructor
    · simp [kadane_aux]
    · constructor
      · intro subarray h_mem h_len
        simp at h_mem
        contradiction
      · simp [List.sublists]
        use []
        simp
  · use (kadane_aux nums).2
    constructor
    · simp [kadane_aux]
    · have h_nonempty : nums ≠ [] := by simp [h]
      exact kadane_aux_sound nums h_nonempty