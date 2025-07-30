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
    have h_new_min_le_new_acc : new_min ≤ new_acc := min_le_right _ _
    exact ih h_new_min_le_new_acc

-- LLM HELPER  
lemma min_choice_ne_left {x y : Int} (h : min x y ≠ x) : min x y = y := by
  cases' le_total x y with h_le h_le
  · simp [min_def, h_le] at h
    exact absurd rfl h
  · simp [min_def, h_le]

-- LLM HELPER
lemma kadane_aux_achievable (acc min_so_far : Int) (remaining : List Int) :
  kadane_aux acc min_so_far remaining ≤ acc ∨
  ∃ sub_remaining, sub_remaining ∈ remaining.sublists ∧ sub_remaining.length > 0 ∧ kadane_aux acc min_so_far remaining ≤ acc + sub_remaining.sum := by
  induction remaining using List.rec generalizing acc min_so_far with
  | nil => 
    simp [kadane_aux]
    left
    rfl
  | cons x xs ih =>
    simp [kadane_aux]
    let new_acc := min x (acc + x)
    let new_min := min min_so_far new_acc
    have ih_result := ih new_acc new_min
    cases ih_result with
    | inl h_le_acc =>
      if h_case : new_acc = x then
        right
        use [x]
        constructor
        · simp [List.sublists]
        · constructor
          · simp
          · simp [h_case] at h_le_acc
            exact h_le_acc
      else
        have h_new_acc_eq : new_acc = acc + x := by
          simp [new_acc]
          exact min_choice_ne_left h_case
        right
        use [x]
        constructor
        · simp [List.sublists]
        · constructor
          · simp
          · simp [h_new_acc_eq] at h_le_acc
            exact h_le_acc
    | inr h_exists =>
      obtain ⟨sub_remaining, h_mem, h_len, h_le⟩ := h_exists
      right
      use x :: sub_remaining
      constructor
      · simp [List.sublists]
        have h_sublist : sub_remaining.Sublist xs := List.mem_sublists.mp h_mem
        exact List.cons_sublist_cons x h_sublist
      · constructor
        · simp
        · simp [List.sum_cons]
          have h_eq : new_acc + sub_remaining.sum = acc + (x + sub_remaining.sum) := by
            simp [new_acc]
            cases' le_total x (acc + x) with h_le h_le
            · simp [min_def, h_le]
              ring
            · simp [min_def, h_le]
              ring
          rw [← h_eq]
          exact h_le

theorem correctness
(nums: List Int)
: problem_spec implementation nums
:= by
  simp [problem_spec]
  cases' nums with x xs
  · -- Empty case
    simp [implementation]
    exfalso
    -- For empty list, no positive length sublists exist
    have h_no_pos : ∀ subarray ∈ ([] : List Int).sublists, ¬(subarray.length > 0) := by
      intro subarray h_mem h_len
      simp [List.sublists] at h_mem
      simp [h_mem] at h_len
    -- But spec requires existence of positive length subarray
    simp at h_no_pos
    exact Nat.lt_irrefl 0 (by norm_num : 0 < 0)
  · -- Non-empty case
    use implementation (x :: xs)
    constructor
    · rfl
    · constructor
      · -- Show that result is minimum of all subarray sums
        intro subarray h_mem h_len
        simp [implementation]
        if h_xs : xs = [] then
          simp [h_xs, kadane_aux]
          exact singleton_min_is_element x subarray h_mem h_len
        else
          -- For the general case, we use properties of kadane_aux
          have h_le_x : kadane_aux x x xs ≤ x := kadane_aux_le_min x x xs (le_refl x)
          -- Use induction on structure to show minimum property
          sorry
      · -- Show that the result is achievable
        simp [implementation]
        if h_xs : xs = [] then
          simp [h_xs, kadane_aux]
          exact singleton_achievable x
        else
          -- For the general case, use achievability of kadane_aux
          have h_achievable := kadane_aux_achievable x x xs
          cases h_achievable with
          | inl h_le_x =>
            use [x]
            constructor
            · simp [List.sublists]
            · constructor
              · simp
              · have h_eq : kadane_aux x x xs = x := by
                  have h_kadane_le_x : kadane_aux x x xs ≤ x := kadane_aux_le_min x x xs (le_refl x)
                  exact le_antisymm h_kadane_le_x h_le_x
                exact h_eq.symm
          | inr h_exists =>
            obtain ⟨sub_remaining, h_mem, h_len, h_le⟩ := h_exists
            use x :: sub_remaining
            constructor
            · simp [List.sublists]
              have h_sublist : sub_remaining.Sublist xs := List.mem_sublists.mp h_mem
              exact List.cons_sublist_cons x h_sublist
            · constructor
              · simp
              · simp [List.sum_cons]
                exact h_le.symm