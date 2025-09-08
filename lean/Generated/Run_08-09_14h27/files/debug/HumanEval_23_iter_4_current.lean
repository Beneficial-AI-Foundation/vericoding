/- 
function_signature: "def strlen(string: str) -> int"
docstring: |
    Return length of given string
test_cases:
  - input: ""
    expected_output: 0
  - input: "abc"
    expected_output: 3
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (string: String): Nat :=
  string.length

def problem_spec
-- function signature
(implementation: String → Nat)
-- inputs
(string: String) :=
-- spec
let spec (result: Nat) :=
-- every character in the string is counted once
result = 0 ↔ string.isEmpty ∧
(0 < result → result - 1 = implementation (string.drop 1))
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
lemma string_length_zero_iff_empty (s : String) : s.length = 0 ↔ s.isEmpty = true := by
  rw [String.isEmpty, String.length]
  constructor
  · intro h
    rw [List.length_eq_zero] at h
    exact h
  · intro h
    rw [List.length_eq_zero]
    exact h

-- LLM HELPER  
lemma string_length_pos_drop (s : String) (h : 0 < s.length) : 
  s.length - 1 = (s.drop 1).length := by
  rw [String.length, String.drop, String.length]
  rw [List.length_drop]
  omega

theorem correctness
(string: String)
: problem_spec implementation string
:= by
  unfold problem_spec implementation
  use string.length
  constructor
  · rfl
  · constructor
    · constructor
      · intro h
        constructor
        · exact string_length_zero_iff_empty string |>.mp h
        · intro h_pos
          rw [h] at h_pos
          omega
      · intro ⟨h_empty, h_drop⟩
        have h_zero := string_length_zero_iff_empty string |>.mpr h_empty
        exact h_zero
    · intro h_pos
      exact string_length_pos_drop string h_pos

-- #test implementation "" = 0
-- #test implementation "abc" = 3