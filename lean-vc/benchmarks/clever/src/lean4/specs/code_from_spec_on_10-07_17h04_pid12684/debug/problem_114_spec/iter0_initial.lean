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
def kadane_aux (nums : List Int) : Int × Int :=
  match nums with
  | [] => (0, 0)
  | x :: xs =>
    let (max_so_far, max_ending_here) := kadane_aux xs
    let new_max_ending_here := max x (max_ending_here + x)
    (max max_so_far new_max_ending_here, new_max_ending_here)

def implementation (nums: List Int) : Int :=
  match nums with
  | [] => 0
  | x :: xs => 
    let (max_so_far, _) := kadane_aux nums
    max_so_far

-- LLM HELPER
lemma sublists_nonempty_exists (nums : List Int) : nums ≠ [] → ∃ subarray ∈ nums.sublists, subarray.length > 0 := by
  intro h
  cases' nums with hd tl
  · contradiction
  · use [hd]
    constructor
    · simp [List.sublists]
      use tl.sublists
      simp [List.map_cons]
      left
      use []
      simp
    · simp

-- LLM HELPER
lemma kadane_aux_correct (nums : List Int) : 
  let (max_so_far, max_ending_here) := kadane_aux nums
  ∀ subarray ∈ nums.sublists, subarray.length > 0 → max_so_far ≤ subarray.sum ∨ max_so_far = subarray.sum := by
  sorry

-- LLM HELPER
lemma kadane_aux_witness (nums : List Int) : 
  let (max_so_far, _) := kadane_aux nums
  nums ≠ [] → ∃ subarray ∈ nums.sublists, subarray.length > 0 ∧ max_so_far = subarray.sum := by
  sorry

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  unfold problem_spec implementation
  cases' h : nums = [] with
  · -- Empty list case
    simp [h]
    use 0
    constructor
    · rfl
    · constructor
      · intro subarray hmem hlen
        simp [h] at hmem
        cases hmem
      · simp [h]
        use []
        simp
  · -- Non-empty list case
    let (max_so_far, _) := kadane_aux nums
    use max_so_far
    constructor
    · rfl
    · constructor
      · intro subarray hmem hlen
        have : ∀ subarray ∈ nums.sublists, subarray.length > 0 → max_so_far ≤ subarray.sum ∨ max_so_far = subarray.sum := 
          kadane_aux_correct nums
        have result := this subarray hmem hlen
        cases result with
        | inl h => exact h
        | inr h => rw [h]
      · exact kadane_aux_witness nums h