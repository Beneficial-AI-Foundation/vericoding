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
lemma kadane_aux_le_min (acc min_so_far : Int) (remaining : List Int) :
  min_so_far ≤ acc → kadane_aux acc min_so_far remaining ≤ min_so_far := by
  intro h
  induction remaining using List.rec generalizing acc min_so_far with
  | nil => simp [kadane_aux]
  | cons x xs ih =>
    simp [kadane_aux]
    let new_acc := min x (acc + x)
    let new_min := min min_so_far new_acc
    have h_new_min_le : new_min ≤ min_so_far := min_le_left _ _
    apply ih
    exact le_trans (min_le_right _ _) h_new_min_le

-- LLM HELPER
lemma kadane_aux_achievable (acc min_so_far : Int) (remaining : List Int) :
  ∃ prefix_sum : Int, 
    (prefix_sum = acc ∨ ∃ sub_remaining, sub_remaining ∈ remaining.sublists ∧ sub_remaining.length > 0 ∧ prefix_sum = acc + sub_remaining.sum) ∧
    kadane_aux acc min_so_far remaining ≤ prefix_sum := by
  induction remaining using List.rec generalizing acc min_so_far with
  | nil => 
    simp [kadane_aux]
    use acc
    simp
  | cons x xs ih =>
    simp [kadane_aux]
    let new_acc := min x (acc + x)
    let new_min := min min_so_far new_acc
    have ih_result := ih new_acc new_min
    obtain ⟨prefix_sum, h_prefix_def, h_kadane_le⟩ := ih_result
    use prefix_sum
    constructor
    · exact h_prefix_def
    · exact h_kadane_le

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
        simp [List.sublists] at h_mem
        simp [h_mem] at h_len
      else
        -- Non-empty case
        cases' nums with x xs
        · contradiction
        · simp [implementation]
          if h_xs : xs = [] then
            simp [h_xs, kadane_aux]
            exact singleton_min_is_element x subarray h_mem h_len
          else
            -- For the general case, we use properties of kadane_aux
            have h_x_le : x ≤ subarray.sum := by
              -- Since subarray is a sublist of nums, and has positive length,
              -- it contains at least one element, and we can show the bound
              have h_subarray_nonempty : subarray ≠ [] := by
                intro h_contra
                simp [h_contra] at h_len
              cases' subarray with y ys
              · contradiction
              · simp [List.sublists, List.Sublist.sublists] at h_mem
                have h_y_in_nums : y ∈ nums := List.Sublist.subset h_mem (List.mem_cons_self y ys)
                simp at h_y_in_nums
                cases h_y_in_nums with
                | inl h_y_eq => 
                  simp [h_y_eq]
                  exact List.single_le_sum _ (List.mem_cons_self y ys)
                | inr h_y_in_xs =>
                  -- y is in xs, so we need a different approach
                  -- We'll use the fact that any element in nums is at least some minimum
                  exact List.single_le_sum _ (List.mem_cons_self y ys)
            exact kadane_aux_le_min x x xs (le_refl x)
    · -- Show that the result is achievable
      if h_empty : nums = [] then
        -- Empty case - contradiction since spec requires positive length subarray
        exfalso
        -- The spec is inconsistent for empty lists
        have h_no_pos : ∀ subarray ∈ nums.sublists, subarray.length = 0 := by
          intro subarray h_mem
          simp [h_empty, List.sublists] at h_mem
          simp [h_mem]
        -- But we need to show existence of positive length subarray
        simp [h_empty] at h_no_pos
        -- This is impossible - empty input makes the spec unsatisfiable
        have : [] ∈ nums.sublists := by simp [List.sublists]
        have : ([] : List Int).length > 0 := by norm_num
        exact Nat.lt_irrefl 0 this
      else
        cases' nums with x xs
        · contradiction
        · simp [implementation]
          if h_xs : xs = [] then
            simp [h_xs, kadane_aux]
            exact singleton_achievable x
          else
            -- For the general case, use achievability of kadane_aux
            have h_achievable := kadane_aux_achievable x x xs
            obtain ⟨prefix_sum, h_prefix_def, h_kadane_le⟩ := h_achievable
            -- We can construct a subarray that achieves the minimum
            use [x]
            constructor
            · simp [List.sublists]
            · constructor
              · simp
              · -- The kadane result equals some achievable sum
                have h_eq : kadane_aux x x xs = x := by
                  -- In the worst case, kadane_aux returns x (the single element)
                  have h_x_achievable : x ≤ kadane_aux x x xs := by
                    -- kadane_aux finds minimum, but it's at least some achievable value
                    cases' xs with y ys
                    · simp [kadane_aux]
                    · simp [kadane_aux]
                      exact min_le_right _ _
                  have h_kadane_le_x : kadane_aux x x xs ≤ x := kadane_aux_le_min x x xs (le_refl x)
                  exact le_antisymm h_kadane_le_x h_x_achievable
                exact h_eq