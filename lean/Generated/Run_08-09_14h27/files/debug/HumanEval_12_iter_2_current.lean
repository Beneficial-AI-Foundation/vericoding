/- 
function_signature: "def longest(strings: List[str]) -> Optional[str]"
docstring: |
    Out of list of strings, return the longest one. Return the first one in case of multiple
    strings of the same length. Return None in case the input list is empty.
test_cases:
  - input: []
    expected_output: None
  - input: ["a", "b", "c"]
    expected_output: "a"
  - input: ["a", "bb", "ccc"]
    expected_output: "ccc"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def find_longest_aux (strings: List String) (current_best: String) : String :=
  match strings with
  | [] => current_best
  | s :: ss => 
    if s.length > current_best.length then
      find_longest_aux ss s
    else
      find_longest_aux ss current_best

def implementation (strings: List String) : Option String :=
  match strings with
  | [] => none
  | s :: ss => some (find_longest_aux ss s)

def problem_spec
-- function signature
(implementation: List String → Option String)
-- inputs
(strings: List String) :=
-- spec
let spec (result: Option String) :=
  (result = none ↔ strings.length = 0) ∨
  (∃ longest, result = some longest ∧
  longest ∈ strings ∧
  ∀ s, s ∈ strings → s.length ≤ longest.length →
  (∃ i, i < strings.length ∧
  strings[i]! = longest ∧ ∀ j < i, strings[j]!.length < longest.length));
-- program termination
∃ result, implementation strings = result ∧
spec result

-- LLM HELPER
lemma find_longest_aux_mem (strings: List String) (current_best: String) :
  current_best ∈ (current_best :: strings) →
  find_longest_aux strings current_best ∈ (current_best :: strings) := by
  intro h_mem
  induction strings generalizing current_best with
  | nil => simp [find_longest_aux]
  | cons s ss ih =>
    simp [find_longest_aux]
    by_cases h : s.length > current_best.length
    · simp [if_pos h]
      have h_s_mem : s ∈ s :: ss := by simp
      have h_combined : s ∈ current_best :: s :: ss := by simp
      specialize ih s h_s_mem
      have ih_result : find_longest_aux ss s ∈ s :: ss := ih
      simp at ih_result ⊢
      exact ih_result
    · simp [if_neg h]
      exact h_mem

-- LLM HELPER
lemma find_longest_aux_maximal (strings: List String) (current_best: String) :
  (∀ s ∈ strings, s.length ≤ current_best.length) →
  find_longest_aux strings current_best = current_best := by
  intro h_all_shorter
  induction strings generalizing current_best with
  | nil => simp [find_longest_aux]
  | cons s ss ih =>
    simp [find_longest_aux]
    have h_s_short : s.length ≤ current_best.length := h_all_shorter s (by simp)
    have h_not_gt : ¬(s.length > current_best.length) := by omega
    simp [if_neg h_not_gt]
    apply ih
    intro t h_t_mem
    exact h_all_shorter t (by simp [h_t_mem])

-- LLM HELPER
lemma find_longest_aux_length (strings: List String) (current_best: String) :
  ∀ s ∈ (current_best :: strings), s.length ≤ (find_longest_aux strings current_best).length := by
  intro s h_mem
  induction strings generalizing current_best with
  | nil => 
    simp [find_longest_aux] at h_mem ⊢
    rw [h_mem]
  | cons t ts ih =>
    simp [find_longest_aux]
    by_cases h : t.length > current_best.length
    · simp [if_pos h]
      specialize ih t
      simp at h_mem ⊢
      cases h_mem with
      | inl h_eq => 
        rw [h_eq]
        apply ih
        simp
      | inr h_rest => 
        cases h_rest with
        | inl h_eq_t =>
          rw [h_eq_t]
          apply ih
          simp
        | inr h_in_ts =>
          apply ih
          simp [h_in_ts]
    · simp [if_neg h]
      simp at h_mem
      cases h_mem with
      | inl h_eq => 
        rw [h_eq]
        apply ih
        simp
      | inr h_rest => 
        cases h_rest with
        | inl h_eq_t => 
          rw [h_eq_t]
          have h_t_le : t.length ≤ current_best.length := by
            have : ¬(t.length > current_best.length) := h
            omega
          have ih_result := ih current_best (by simp)
          omega
        | inr h_in_ts => 
          apply ih
          simp [h_in_ts]

theorem correctness
(strings: List String)
: problem_spec implementation strings
:= by
  unfold problem_spec
  use implementation strings
  constructor
  · rfl
  · cases strings with
    | nil => 
      simp [implementation]
      left
      simp
    | cons s ss =>
      simp [implementation]
      right
      use find_longest_aux ss s
      constructor
      · rfl
      · constructor
        · apply find_longest_aux_mem
          simp
        · intro t h_mem h_len
          use 0
          constructor
          · simp
          · intro j h_j_lt
            have : j < 1 := by simp at h_j_lt; exact h_j_lt
            have : j = 0 := by omega
            omega

-- #test implementation ["a", "b", "c"] = some "a"
-- #test implementation ["a", "bb", "ccc"] = some "ccc"
-- #test implementation [] = none