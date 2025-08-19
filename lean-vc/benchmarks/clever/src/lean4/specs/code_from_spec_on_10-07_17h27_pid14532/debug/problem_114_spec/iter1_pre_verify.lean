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
def min_subarray_sum_aux (nums : List Int) : Int :=
  match nums with
  | [] => 0
  | [x] => x
  | x :: xs => 
    let rest_min := min_subarray_sum_aux xs
    let current_min := (List.scanl (· + ·) x xs).minimum?
    min rest_min (current_min.getD x)

-- LLM HELPER
def all_nonempty_sublists (nums : List Int) : List (List Int) :=
  nums.sublists.filter (fun l => l.length > 0)

-- LLM HELPER
def min_sum_of_nonempty_sublists (nums : List Int) : Int :=
  match all_nonempty_sublists nums with
  | [] => 0
  | l :: ls => (l.sum :: ls.map List.sum).minimum

def implementation (nums: List Int) : Int := 
  match nums with
  | [] => 0
  | _ => min_sum_of_nonempty_sublists nums

-- LLM HELPER
lemma nonempty_sublists_exist (nums : List Int) (h : nums ≠ []) : 
  ∃ subarray ∈ nums.sublists, subarray.length > 0 := by
  cases' nums with x xs
  · contradiction
  · use [x]
    constructor
    · simp [List.sublists]
      left
      simp [List.sublists']
    · simp

-- LLM HELPER
lemma min_achieves_minimum (l : List Int) (h : l ≠ []) : 
  l.minimum ∈ l ∧ ∀ x ∈ l, l.minimum ≤ x := by
  simp [List.minimum]
  cases' l with a as
  · contradiction
  · simp [List.minimum_cons]
    apply List.le_min_iff.mp
    rfl

-- LLM HELPER
lemma all_nonempty_sublists_spec (nums : List Int) : 
  ∀ l ∈ all_nonempty_sublists nums, l ∈ nums.sublists ∧ l.length > 0 := by
  simp [all_nonempty_sublists]
  intro l h1 h2
  exact ⟨h1, h2⟩

-- LLM HELPER
lemma min_sum_is_minimum (nums : List Int) (h : nums ≠ []) :
  let result := min_sum_of_nonempty_sublists nums
  (∀ subarray ∈ nums.sublists, subarray.length > 0 → result ≤ subarray.sum) ∧
  (∃ subarray ∈ nums.sublists, subarray.length > 0 ∧ result = subarray.sum) := by
  simp [min_sum_of_nonempty_sublists]
  have h_exists : all_nonempty_sublists nums ≠ [] := by
    cases' nums with x xs
    · contradiction
    · simp [all_nonempty_sublists, List.sublists]
      use [x]
      simp
  cases' all_nonempty_sublists nums with first rest
  · contradiction
  · simp [List.minimum_cons]
    constructor
    · intro subarray h_mem h_len
      have h_in_all : subarray ∈ all_nonempty_sublists nums := by
        simp [all_nonempty_sublists]
        exact ⟨h_mem, h_len⟩
      simp [all_nonempty_sublists] at h_in_all
      have h_sum_in : subarray.sum ∈ (first.sum :: rest.map List.sum) := by
        cases' h_in_all with h1 h2
        · simp [h1]
        · simp
          right
          exact List.mem_map_of_mem List.sum h2
      exact List.minimum_le h_sum_in
    · have h_min_in : (first.sum :: rest.map List.sum).minimum ∈ (first.sum :: rest.map List.sum) := by
        apply List.minimum_mem
        simp
      cases' h_min_in with h1 h2
      · use first
        have h_first_in : first ∈ all_nonempty_sublists nums := by
          simp [all_nonempty_sublists]
        have h_spec := all_nonempty_sublists_spec nums first h_first_in
        exact ⟨h_spec.1, h_spec.2, h1.symm⟩
      · simp at h2
        obtain ⟨l, h_l_in, h_eq⟩ := h2
        use l
        have h_l_in_all : l ∈ all_nonempty_sublists nums := by
          simp [all_nonempty_sublists]
          exact h_l_in
        have h_spec := all_nonempty_sublists_spec nums l h_l_in_all
        exact ⟨h_spec.1, h_spec.2, h_eq.symm⟩

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  simp [problem_spec, implementation]
  cases' h : nums with x xs
  · simp
    use 0
    constructor
    · rfl
    · simp [List.sublists]
      constructor
      · intro subarray h_mem h_len
        simp at h_mem
      · intro subarray h_mem h_len
        simp at h_mem
  · simp
    use min_sum_of_nonempty_sublists nums
    constructor
    · rfl
    · rw [← h]
      apply min_sum_is_minimum
      rw [h]
      simp