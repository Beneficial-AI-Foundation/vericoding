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
lemma string_length_zero_iff_empty (s : String) : s.length = 0 ↔ s.isEmpty := by
  simp [String.isEmpty, String.length]

-- LLM HELPER  
lemma string_length_pos_drop (s : String) (h : 0 < s.length) : 
  s.length - 1 = (s.drop 1).length := by
  simp [String.length, String.drop]
  sorry

theorem correctness
(string: String)
: problem_spec implementation string
:= by
  unfold problem_spec implementation
  simp
  constructor
  · exact ⟨string.length, rfl, string_length_zero_iff_empty string, 
      fun h => string_length_pos_drop string h⟩

-- #test implementation "" = 0
-- #test implementation "abc" = 3