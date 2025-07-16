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
  min_so_far ≤ acc → kadane_aux acc min_so_far remaining ≤ acc := by
  intro h
  induction remaining using List.rec generalizing acc min_so_far with
  | nil => simp [kadane_aux]; exact h
  | cons x xs ih =>
    simp [kadane_aux]
    let new_acc := min x (acc + x)
    let new_min := min min_so_far new_acc
    have h_new_min_le : new_min ≤ min_so_far := min_le_left _ _
    have h_new_min_le_new_acc : new_min ≤ new_acc := min_le_right _ _
    have h_new_min_le_acc : new_min ≤ acc := by
      calc new_min
        ≤ min_so_far := h_new_min_le
        _ ≤ acc := h
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
    exact le_refl _
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

-- LLM HELPER
lemma kadane_aux_is_min_over_all_sublists (acc min_so_far : Int) (remaining : List Int) :
  min_so_far ≤ acc →
  ∀ subarray ∈ remaining.sublists, subarray.length > 0 → kadane_aux acc min_so_far remaining ≤ acc + subarray.sum := by
  intro h_min_le subarray h_mem h_len
  induction remaining using List.rec generalizing acc min_so_far with
  | nil => 
    simp [List.sublists] at h_mem
    simp [h_mem] at h_len
  | cons x xs ih =>
    simp [kadane_aux]
    let new_acc := min x (acc + x)
    let new_min := min min_so_far new_acc
    have h_new_min_le : new_min ≤ new_acc := min_le_right _ _
    simp [List.sublists] at h_mem
    cases h_mem with
    | inl h_nil =>
      simp [h_nil] at h_len
    | inr h_cons =>
      cases h_cons with
      | inl h_singleton =>
        simp [h_singleton, List.sum_cons]
        have h_le_x : kadane_aux new_acc new_min xs ≤ new_acc := kadane_aux_le_min new_acc new_min xs h_new_min_le
        exact le_trans h_le_x (min_le_left _ _)
      | inr h_rest =>
        obtain ⟨sub_xs, h_mem_xs, h_eq⟩ := h_rest
        simp [h_eq, List.sum_cons]
        have h_ih := ih new_acc new_min h_new_min_le sub_xs h_mem_xs
        have h_len_sub : sub_xs.length > 0 := by
          simp [← h_eq] at h_len
          exact Nat.pos_of_ne_zero (Nat.succ_ne_zero _)
        have h_le := h_ih h_len_sub
        exact le_trans h_le (by simp [add_assoc])

theorem correctness
(nums: List Int)
: problem_spec implementation nums
:= by
  simp [problem_spec]
  cases' nums with x xs
  · -- Empty case - no positive length sublists exist
    simp [implementation]
    exfalso
    have h_no_pos : ∀ subarray ∈ ([] : List Int).sublists, subarray.length > 0 → False := by
      intro subarray h_mem h_len
      simp [List.sublists] at h_mem
      simp [h_mem] at h_len
    have h_exists : ∃ subarray ∈ ([] : List Int).sublists, subarray.length > 0 := by
      use []
      constructor
      · simp [List.sublists]
      · norm_num
    obtain ⟨subarray, h_mem, h_len⟩ := h_exists
    exact h_no_pos subarray h_mem h_len
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
          -- Use the general property of kadane_aux
          have h_le_x : kadane_aux x x xs ≤ x := kadane_aux_le_min x x xs (le_refl x)
          -- The algorithm explores all possible starting points
          have h_general : ∀ subarray ∈ (x :: xs).sublists, subarray.length > 0 → kadane_aux x x xs ≤ subarray.sum := by
            intro sub h_mem_sub h_len_sub
            simp [List.sublists] at h_mem_sub
            cases h_mem_sub with
            | inl h_nil =>
              simp [h_nil] at h_len_sub
            | inr h_cons =>
              cases h_cons with
              | inl h_singleton =>
                simp [h_singleton]
                exact h_le_x
              | inr h_rest =>
                obtain ⟨sub_xs, h_mem_xs, h_eq⟩ := h_rest
                simp [h_eq, List.sum_cons]
                have h_aux_prop := kadane_aux_is_min_over_all_sublists x x xs (le_refl x)
                have h_len_pos : sub_xs.length > 0 := by
                  simp [← h_eq] at h_len_sub
                  exact Nat.pos_of_ne_zero (Nat.succ_ne_zero _)
                exact h_aux_prop sub_xs h_mem_xs h_len_pos
          exact h_general subarray h_mem h_len
      · -- Show that the result is achievable
        simp [implementation]
        if h_xs : xs = [] then
          simp [h_xs, kadane_aux]
          exact singleton_achievable x
        else
          -- Use achievability of kadane_aux
          have h_achievable := kadane_aux_achievable x x xs
          cases h_achievable with
          | inl h_le_x =>
            use [x]
            constructor
            · simp [List.sublists]
            · constructor
              · simp
              · have h_kadane_le_x : kadane_aux x x xs ≤ x := kadane_aux_le_min x x xs (le_refl x)
                exact le_antisymm h_kadane_le_x h_le_x
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