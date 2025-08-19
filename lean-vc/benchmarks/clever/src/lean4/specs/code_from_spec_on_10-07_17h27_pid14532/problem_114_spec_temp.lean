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
def all_nonempty_sublists (nums : List Int) : List (List Int) :=
  nums.sublists.filter (fun l => l.length > 0)

-- LLM HELPER
def min_sum_of_nonempty_sublists (nums : List Int) : Int :=
  match all_nonempty_sublists nums with
  | [] => 0
  | l :: ls => 
    let sums := l.sum :: ls.map List.sum
    match sums.min? with
    | some min_val => min_val
    | none => 0

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
      apply List.Sublist.cons2
      exact List.Sublist.nil
    · simp

-- LLM HELPER
lemma all_nonempty_sublists_spec (nums : List Int) : 
  ∀ l ∈ all_nonempty_sublists nums, l ∈ nums.sublists ∧ l.length > 0 := by
  simp [all_nonempty_sublists]
  intro l h1 h2
  exact ⟨h1, h2⟩

-- LLM HELPER
lemma all_nonempty_sublists_nonempty (nums : List Int) (h : nums ≠ []) : 
  all_nonempty_sublists nums ≠ [] := by
  simp [all_nonempty_sublists]
  cases' nums with x xs
  · contradiction
  · use [x]
    constructor
    · simp [List.sublists]
      apply List.Sublist.cons2
      exact List.Sublist.nil
    · simp

-- LLM HELPER
lemma List.min?_eq_some_iff_mem_and_minimal {α : Type*} [LinearOrder α] (l : List α) (m : α) :
  l.min? = some m ↔ m ∈ l ∧ ∀ x ∈ l, m ≤ x := by
  constructor
  · intro h
    cases' l with hd tl
    · simp at h
    · simp [List.min?] at h
      rw [List.minimum_eq_some_iff] at h
      exact h
  · intro ⟨h_mem, h_min⟩
    cases' l with hd tl
    · simp at h_mem
    · simp [List.min?]
      rw [List.minimum_eq_some_iff]
      exact ⟨h_mem, h_min⟩

-- LLM HELPER
lemma min_sum_is_minimum (nums : List Int) (h : nums ≠ []) :
  let result := min_sum_of_nonempty_sublists nums
  (∀ subarray ∈ nums.sublists, subarray.length > 0 → result ≤ subarray.sum) ∧
  (∃ subarray ∈ nums.sublists, subarray.length > 0 ∧ result = subarray.sum) := by
  simp [min_sum_of_nonempty_sublists]
  have h_exists : all_nonempty_sublists nums ≠ [] := all_nonempty_sublists_nonempty nums h
  cases' all_nonempty_sublists nums with first rest
  · contradiction
  · simp
    let sums := first.sum :: rest.map List.sum
    have h_sums_nonempty : sums ≠ [] := by simp [sums]
    cases' h_min : sums.min? with min_val
    · simp at h_min
      have : sums = [] := List.min?_eq_none_iff.mp h_min
      contradiction
    · simp [min_val]
      constructor
      · intro subarray h_mem h_len
        have h_in_all : subarray ∈ all_nonempty_sublists nums := by
          simp [all_nonempty_sublists]
          exact ⟨h_mem, h_len⟩
        have h_first_or_rest : subarray = first ∨ subarray ∈ rest := by
          simp [all_nonempty_sublists] at h_in_all
          rw [List.mem_cons] at h_in_all
          exact h_in_all
        have h_sum_in : subarray.sum ∈ sums := by
          cases' h_first_or_rest with h1 h2
          · simp [sums, h1]
          · simp [sums]
            right
            exact List.mem_map_of_mem List.sum h2
        have h_min_le : min_val ≤ subarray.sum := by
          rw [List.min?_eq_some_iff_mem_and_minimal] at h_min
          exact h_min.2 subarray.sum h_sum_in
        exact h_min_le
      · have h_min_in : min_val ∈ sums := by
          rw [List.min?_eq_some_iff_mem_and_minimal] at h_min
          exact h_min.1
        simp [sums] at h_min_in
        cases' h_min_in with h1 h2
        · use first
          have h_first_in : first ∈ all_nonempty_sublists nums := by
            simp [all_nonempty_sublists]
            exact List.mem_cons_self first rest
          have h_spec := all_nonempty_sublists_spec nums first h_first_in
          exact ⟨h_spec.1, h_spec.2, h1.symm⟩
        · simp at h2
          obtain ⟨l, h_l_in, h_eq⟩ := h2
          use l
          have h_l_in_all : l ∈ all_nonempty_sublists nums := by
            simp [all_nonempty_sublists]
            exact List.mem_cons_of_mem first h_l_in
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
        rw [h_mem] at h_len
        simp at h_len
      · intro subarray h_mem h_len
        simp at h_mem
        rw [h_mem] at h_len
        simp at h_len
  · simp
    use min_sum_of_nonempty_sublists (x :: xs)
    constructor
    · rfl
    · apply min_sum_is_minimum
      simp