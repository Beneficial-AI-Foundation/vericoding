/- 
function_signature: "def sorted_list_sum(lst: List[str]) -> List[str]"
docstring: |
    Write a function that accepts a list of strings as a parameter,
    deletes the strings that have odd lengths from it,
    and returns the resulted list with a sorted order,
    The list is always a list of strings and never an array of numbers,
    and it may contain duplicates.
    The order of the list should be ascending by length of each word, and you
    should return the list sorted by that rule.
    If two words have the same length, sort the list alphabetically.
    The function should return a list of strings in sorted order.
    You may assume that all words will have the same length.
test_cases:
  - input: ["aa", "a", "aaa"]
    output: ["aa"]
  - input: ["ab", "a", "aaa", "cd"]
    output: ["ab", "cd"]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def custom_compare (s1 s2 : String) : Bool :=
  if s1.length < s2.length then true
  else if s1.length > s2.length then false
  else s1 < s2

def implementation (lst: List String) : List String :=
  (lst.filter (fun s => Even s.length)).toArray.qsort (fun s1 s2 => custom_compare s1 s2) |>.toList

def problem_spec
-- function signature
(impl: List String → List String)
-- inputs
(lst: List String) :=
-- spec
let spec (result: List String) :=
match result with
| [] => ∀ str ∈ lst, Odd str.length
| head::tail =>
  Even head.length ∧
  (∀ str ∈ lst,
    Odd str.length ∨
    str.length > head.length ∨
    str.length = head.length ∧ str ≥ head)
  ∧ impl (lst.erase head) = tail
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma filter_even_preserves_membership (lst : List String) (s : String) :
  s ∈ lst.filter (fun x => Even x.length) ↔ s ∈ lst ∧ Even s.length := by
  simp [List.mem_filter]

-- LLM HELPER
lemma qsort_preserves_membership {α : Type*} (arr : Array α) (cmp : α → α → Bool) (x : α) :
  x ∈ arr.qsort cmp ↔ x ∈ arr := by
  simp [Array.mem_qsort]

-- LLM HELPER
lemma implementation_preserves_even_length (lst : List String) (s : String) :
  s ∈ implementation lst → Even s.length := by
  simp [implementation]
  intro h
  rw [← Array.mem_toList] at h
  rw [qsort_preserves_membership] at h
  rw [Array.mem_toList] at h
  rw [filter_even_preserves_membership] at h
  exact h.2

-- LLM HELPER
lemma implementation_subset_original (lst : List String) (s : String) :
  s ∈ implementation lst → s ∈ lst := by
  simp [implementation]
  intro h
  rw [← Array.mem_toList] at h
  rw [qsort_preserves_membership] at h
  rw [Array.mem_toList] at h
  rw [filter_even_preserves_membership] at h
  exact h.1

theorem correctness
(lst: List String)
: problem_spec implementation lst := by
  simp [problem_spec]
  use implementation lst
  constructor
  · rfl
  · cases' h : implementation lst with head tail
    · -- Case: implementation lst = []
      simp [h]
      intro str str_in_lst
      by_contra h_even
      have : str ∈ implementation lst := by
        simp [implementation]
        rw [← Array.mem_toList]
        rw [qsort_preserves_membership]
        rw [Array.mem_toList]
        rw [filter_even_preserves_membership]
        exact ⟨str_in_lst, h_even⟩
      rw [h] at this
      exact this
    · -- Case: implementation lst = head :: tail
      constructor
      · -- Prove Even head.length
        have head_in_impl : head ∈ implementation lst := by
          rw [h]
          simp
        exact implementation_preserves_even_length lst head head_in_impl
      · constructor
        · -- Prove the ordering property
          intro str str_in_lst
          by_cases h_odd : Odd str.length
          · left
            exact h_odd
          · push_neg at h_odd
            have h_even_str : Even str.length := by
              rw [Nat.odd_iff_not_even] at h_odd
              exact h_odd
            have str_in_filtered : str ∈ lst.filter (fun s => Even s.length) := by
              rw [filter_even_preserves_membership]
              exact ⟨str_in_lst, h_even_str⟩
            have str_in_impl : str ∈ implementation lst := by
              simp [implementation]
              rw [← Array.mem_toList]
              rw [qsort_preserves_membership]
              rw [Array.mem_toList]
              exact str_in_filtered
            rw [h] at str_in_impl
            cases' str_in_impl with str_eq_head str_in_tail
            · -- str = head case
              right
              right
              constructor
              · rw [str_eq_head]
              · rw [str_eq_head]
            · -- str ∈ tail case
              sorry -- This requires more detailed analysis of the sorting property
        · -- Prove impl (lst.erase head) = tail
          sorry -- This would require proving properties about how erase interacts with our implementation