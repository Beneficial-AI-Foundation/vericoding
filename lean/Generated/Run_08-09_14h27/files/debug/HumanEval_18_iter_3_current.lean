/- 
function_signature: "def how_many_times(string: str, substring: str) -> int"
docstring: |
  Find how many times a given substring can be found in the original string. Count overlaping cases.
test_cases:
  - input:
      - ""
      - "a"
    expected_output: 0
  - input:
      - "aaa"
      - "a"
    expected_output: 3
  - input:
      - "aaaa"
      - "aa"
    expected_output: 3
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def count_overlapping_aux (string: String) (substring: String) (start_pos: Nat) : Nat :=
  if h : start_pos + substring.length > string.length then 0
  else if string.extract ⟨start_pos⟩ ⟨start_pos + substring.length⟩ = substring then
    1 + count_overlapping_aux string substring (start_pos + 1)
  else
    count_overlapping_aux string substring (start_pos + 1)
termination_by string.length - start_pos
decreasing_by
  simp_wf
  have h_bound : start_pos + substring.length ≤ string.length := by omega
  omega

def implementation (string: String) (substring: String) : Nat :=
  if substring.length = 0 then 
    if string.length = 0 then 1 else string.length + 1
  else
    count_overlapping_aux string substring 0

def problem_spec
-- function signature
(implementation: String → String → Nat)
-- inputs
(string substring: String) :=
-- spec
let spec (result: Nat) :=
(string.length < substring.length → result = 0)
∧
(string.length = substring.length →
((string = substring ↔ result = 1) ∧
(substring ≠ string ↔ result = 0)))
∧
(substring.length < string.length  →
let subtring_start_idx := {i: Nat | i ≤ string.length - substring.length};
let substring_occurrences := {i ∈ subtring_start_idx | (string.take (i + substring.length)).drop i = substring };
result = substring_occurrences.toFinset.card);
-- program termination
∃ result, implementation string substring = result ∧
spec result

-- LLM HELPER
lemma extract_eq_take_drop (s: String) (i j: Nat) : 
  s.extract ⟨i⟩ ⟨j⟩ = (s.take j).drop i := by
  rfl

theorem correctness
(string: String)
(substring: String)
: problem_spec implementation string substring
:= by
  unfold problem_spec
  use implementation string substring
  constructor
  · rfl
  · unfold implementation
    by_cases h1 : substring.length = 0
    · -- substring.length = 0
      simp [h1]
      by_cases h2 : string.length = 0
      · -- string.length = 0
        simp [h2]
        constructor
        · intro h; simp
        constructor
        · constructor
          · intro h_eq
            simp [h2, h1] at h_eq
            rfl
          · intro h_one
            simp [h2, h1]
        · intro h; simp at h
      · -- string.length ≠ 0
        simp [h2]
        constructor
        · intro h; simp at h
          have : string.length > 0 := Nat.pos_of_ne_zero h2
          omega
        constructor
        · intro h_eq; simp at h_eq
          have : string.length = 0 := by simp [h_eq]
          contradiction
        · intro h; simp at h
          have : 0 < string.length := Nat.pos_of_ne_zero h2
          omega
    · -- substring.length > 0
      simp [h1]
      have h_pos : 0 < substring.length := Nat.pos_of_ne_zero h1
      constructor
      · intro h_lt
        simp [count_overlapping_aux]
        have : 0 + substring.length > string.length := by omega
        simp [this]
      constructor
      · intro h_eq
        constructor
        · constructor
          · intro h_str_eq
            simp [count_overlapping_aux]
            have : ¬(0 + substring.length > string.length) := by omega
            simp [this]
            rw [extract_eq_take_drop]
            simp [h_eq, h_str_eq]
            have : (string.take substring.length).drop 0 = string := by simp [h_eq]
            simp [h_str_eq, this]
          · intro h_result_one
            by_contra h_str_neq
            simp [count_overlapping_aux] at h_result_one
            have : ¬(0 + substring.length > string.length) := by omega
            simp [this] at h_result_one
            rw [extract_eq_take_drop] at h_result_one
            simp [h_eq] at h_result_one
            by_cases h_match : (string.take substring.length).drop 0 = substring
            · simp [h_match] at h_result_one
              have : (string.take substring.length).drop 0 = string := by simp [h_eq]
              rw [this] at h_match
              contradiction
            · simp [h_match] at h_result_one
        · constructor
          · intro h_str_neq
            simp [count_overlapping_aux]
            have : ¬(0 + substring.length > string.length) := by omega
            simp [this]
            rw [extract_eq_take_drop]
            simp [h_eq]
            have : (string.take substring.length).drop 0 = string := by simp [h_eq]
            simp [this, h_str_neq]
          · intro h_result_zero
            by_contra h_str_eq
            simp [count_overlapping_aux] at h_result_zero
            have : ¬(0 + substring.length > string.length) := by omega
            simp [this] at h_result_zero
            rw [extract_eq_take_drop] at h_result_zero
            simp [h_eq, h_str_eq] at h_result_zero
            have : (string.take substring.length).drop 0 = string := by simp [h_eq]
            simp [this] at h_result_zero
      · intro h_gt
        -- For the complex case where string is longer than substring,
        -- we would need to prove correspondence between aux function and set cardinality
        -- This requires structural induction on the aux function
        sorry