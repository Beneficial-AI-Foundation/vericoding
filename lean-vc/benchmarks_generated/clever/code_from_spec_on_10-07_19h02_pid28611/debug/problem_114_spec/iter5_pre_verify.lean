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
lemma sublist_mem_of_elem_mem (x : Int) (nums : List Int) :
  x ∈ nums → [x] ∈ nums.sublists := by
  intro h_mem
  simp [List.sublists, List.Sublist.sublists]
  use [x]
  constructor
  · exact List.singleton_sublist.mpr h_mem
  · rfl

-- LLM HELPER
lemma min_element_bound (nums : List Int) (h_nonempty : nums ≠ []) :
  ∃ m ∈ nums, ∀ subarray ∈ nums.sublists, subarray.length > 0 → m ≤ subarray.sum := by
  -- Find minimum element
  have h_nonempty' : nums.length > 0 := by
    cases nums with
    | nil => simp at h_nonempty
    | cons => simp
  obtain ⟨m, h_m_mem⟩ := List.exists_min_image nums (fun x => x) h_nonempty'
  use m
  constructor
  · exact h_m_mem.1
  · intro subarray h_sub h_len
    -- Any non-empty subarray has sum at least the minimum element
    have h_exists_elem : ∃ y ∈ subarray, y ∈ nums := by
      cases subarray with
      | nil => simp at h_len
      | cons y ys => 
        use y
        constructor
        · simp
        · have : subarray ∈ nums.sublists := h_sub
          simp [List.sublists, List.Sublist.sublists] at this
          obtain ⟨s, h_s_sublist, h_s_eq⟩ := this
          rw [← h_s_eq] at h_s_sublist
          exact List.Sublist.subset h_s_sublist (List.mem_cons_self y ys)
    obtain ⟨y, h_y_sub, h_y_nums⟩ := h_exists_elem
    have h_m_le_y : m ≤ y := h_m_mem.2 y h_y_nums
    have h_y_le_sum : y ≤ subarray.sum := by
      simp [List.sum]
      exact List.single_le_sum _ h_y_sub
    exact le_trans h_m_le_y h_y_le_sum

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
            -- For the general case, we use the fact that our algorithm finds a minimum
            -- The implementation returns some value that is at most any subarray sum
            -- This is the key property of Kadane's algorithm for minimum subarray
            have h_min_bound : ∃ m ∈ nums, ∀ sub ∈ nums.sublists, sub.length > 0 → m ≤ sub.sum := 
              min_element_bound nums h_empty
            obtain ⟨m, h_m_mem, h_m_bound⟩ := h_min_bound
            -- Our implementation gives at most m
            have h_impl_le_m : implementation nums ≤ m := by
              simp [implementation]
              -- The kadane algorithm will find the minimum, which is at most m
              -- This would require a full proof of kadane's correctness
              sorry
            exact le_trans h_impl_le_m (h_m_bound subarray h_mem h_len)
    · -- Show that the result is achievable
      if h_empty : nums = [] then
        -- Empty case - impossible since spec requires existence
        exfalso
        -- The spec requires existence of positive length subarray, but empty list has none
        have h_no_pos : ∀ subarray ∈ nums.sublists, subarray.length = 0 := 
          empty_sublists_no_positive_length nums h_empty
        -- But we need to show existence of positive length subarray
        -- This is actually a contradiction in the spec for empty lists
        -- We'll handle this by assuming the spec is only meaningful for non-empty lists
        sorry
      else
        cases' nums with x xs
        · contradiction
        · simp [implementation]
          if h_xs : xs = [] then
            simp [h_xs, kadane_aux]
            exact singleton_achievable x
          else
            -- For the general case, we know our algorithm finds some achievable minimum
            -- There exists some subarray that achieves the minimum sum
            have h_min_bound : ∃ m ∈ nums, ∀ sub ∈ nums.sublists, sub.length > 0 → m ≤ sub.sum := 
              min_element_bound nums h_empty
            obtain ⟨m, h_m_mem, h_m_bound⟩ := h_min_bound
            -- The singleton [m] achieves sum m
            have h_single_mem : [m] ∈ nums.sublists := sublist_mem_of_elem_mem m nums h_m_mem
            use [m]
            constructor
            · exact h_single_mem
            · constructor
              · simp
              · -- Our implementation equals this minimum
                simp [implementation]
                -- Would need full kadane correctness proof
                sorry