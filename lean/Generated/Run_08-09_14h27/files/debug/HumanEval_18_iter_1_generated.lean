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
  if start_pos + substring.length > string.length then 0
  else if string.extract ⟨start_pos⟩ ⟨start_pos + substring.length⟩ = substring then
    1 + count_overlapping_aux string substring (start_pos + 1)
  else
    count_overlapping_aux string substring (start_pos + 1)

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
  simp [String.extract]

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
    split_ifs with h1
    · -- substring.length = 0
      split_ifs with h2
      · -- string.length = 0
        simp [h1, h2]
        constructor
        · intro h; simp
        constructor
        · constructor
          · intro h_eq; simp at h_eq
            simp [h_eq]
          · intro h_one; simp at h_one
        · intro h; simp at h
      · -- string.length ≠ 0
        simp [h1]
        constructor
        · intro h; simp at h
          have : string.length ≥ 1 := Nat.pos_of_ne_zero h2
          omega
        constructor
        · intro h_eq; simp at h_eq
          have : string.length = 0 := by simp [h_eq]
          contradiction
        · intro h; simp at h
          have : 0 < string.length := Nat.pos_of_ne_zero h2
          omega
    · -- substring.length > 0
      have h_pos : 0 < substring.length := Nat.pos_of_ne_zero h1
      unfold count_overlapping_aux
      simp
      constructor
      · intro h_lt
        simp [h_lt]
        split_ifs
        · omega
        · rfl
      constructor
      · intro h_eq
        constructor
        · constructor
          · intro h_str_eq
            simp [h_eq, h_str_eq]
            split_ifs with h3
            · simp at h3
              rw [extract_eq_take_drop]
              simp [h_str_eq]
            · simp at h3
              omega
          · intro h_result_one
            by_cases h4 : string.extract ⟨0⟩ ⟨substring.length⟩ = substring
            · rw [extract_eq_take_drop] at h4
              simp [h_eq] at h4
              exact h4
            · split_ifs at h_result_one with h5
              · contradiction
              · simp at h_result_one
        · constructor
          · intro h_str_neq
            by_cases h4 : string.extract ⟨0⟩ ⟨substring.length⟩ = substring
            · rw [extract_eq_take_drop] at h4
              simp [h_eq] at h4
              contradiction
            · split_ifs with h5
              · contradiction  
              · simp
          · intro h_result_zero
            by_cases h4 : string.extract ⟨0⟩ ⟨substring.length⟩ = substring
            · split_ifs at h_result_zero with h5
              · simp at h_result_zero
              · simp at h_result_zero
            · rw [extract_eq_take_drop] at h4
              simp [h_eq] at h4
              exact h4
      · intro h_gt
        simp [h_gt]
        -- This case requires a more complex proof about the correspondence 
        -- between our auxiliary function and the specification
        sorry

-- #test implementation "aaa" "a" = 3
-- #test implementation "aaaa" "aa" = 3
-- #test implementation "" "a" = 0
-- #test implementation "a" "" = 1
-- #test implementation "a" "a" = 1