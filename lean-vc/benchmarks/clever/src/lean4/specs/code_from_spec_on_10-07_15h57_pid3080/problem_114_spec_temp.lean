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
def min_subarray_sum_aux (nums: List Int) (current_sum: Int) (min_so_far: Int) : Int :=
  match nums with
  | [] => min_so_far
  | head :: tail =>
    let new_current := Int.min head (current_sum + head)
    let new_min := Int.min min_so_far new_current
    min_subarray_sum_aux tail new_current new_min

def implementation (nums: List Int) : Int := 
  match nums with
  | [] => 0
  | head :: tail => min_subarray_sum_aux nums head head

-- LLM HELPER
lemma Int.min_le_left (a b : Int) : Int.min a b ≤ a := by
  simp [Int.min]
  split
  · rfl
  · linarith

-- LLM HELPER
lemma Int.min_le_right (a b : Int) : Int.min a b ≤ b := by
  simp [Int.min]
  split
  · linarith
  · rfl

-- LLM HELPER
lemma List.mem_sublists_singleton {α : Type*} (l : List α) (x : α) (h : x ∈ l) : [x] ∈ l.sublists := by
  rw [List.mem_sublists]
  exact List.singleton_sublist.mpr h

-- LLM HELPER
lemma List.singleton_sublist_of_mem {α : Type*} (l : List α) (x : α) (h : x ∈ l) : [x] <+ l := by
  exact List.singleton_sublist.mpr h

-- LLM HELPER
lemma min_subarray_sum_aux_bounded (nums: List Int) (current_sum: Int) (min_so_far: Int) (x : Int) (h : x ∈ nums) :
  min_subarray_sum_aux nums current_sum min_so_far ≤ x := by
  induction nums generalizing current_sum min_so_far with
  | nil => simp at h
  | cons head tail ih =>
    simp [min_subarray_sum_aux]
    cases' h with h h
    · simp [h]
      let new_current := Int.min head (current_sum + head)
      let new_min := Int.min min_so_far new_current
      have h1 : new_min ≤ new_current := Int.min_le_right min_so_far new_current
      have h2 : new_current ≤ head := Int.min_le_left head (current_sum + head)
      apply ih
      exact h
    · let new_current := Int.min head (current_sum + head)
      let new_min := Int.min min_so_far new_current
      apply ih
      exact h

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  unfold problem_spec
  cases' nums with head tail
  · -- Empty list case
    use 0
    constructor
    · simp [implementation]
    · constructor
      · intro subarray h_mem h_len
        simp at h_mem
        exfalso
        exact List.length_pos_iff_ne_nil.mp h_len h_mem
      · simp
        exfalso
        have : [] ∈ [].sublists := by simp [List.sublists]
        have : ([] : List Int).length > 0 := by assumption
        simp at this
  · -- Non-empty list case
    use head
    constructor
    · simp [implementation, min_subarray_sum_aux]
    · constructor
      · intro subarray h_mem h_len
        rw [List.mem_sublists] at h_mem
        cases' subarray with s_head s_tail
        · simp at h_len
        · have : s_head ∈ (head :: tail) := by
            have : s_head ∈ (s_head :: s_tail) := List.mem_cons_self s_head s_tail
            exact List.Sublist.subset h_mem this
          cases' this with h_eq h_mem_tail
          · simp [h_eq, List.sum]
          · simp [List.sum]
            linarith
      · use [head]
        constructor
        · rw [List.mem_sublists]
          exact List.singleton_sublist_of_mem (head :: tail) head (List.mem_cons_self head tail)
        · constructor
          · simp
          · simp [List.sum]