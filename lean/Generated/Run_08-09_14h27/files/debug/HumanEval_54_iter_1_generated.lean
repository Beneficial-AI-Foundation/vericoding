/- 
function_signature: "def same_chars(s0: string, s1: string) -> Bool"
docstring: Check if two words have the same characters.
test_cases:
  - input: ['eabcdzzzz', 'dddzzzzzzzddeddabc']
    expected_output: True
  - input: ['eabcd', 'dddddddabc']
    expected_output: False
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def chars_set (s : String) : Finset Char := s.toList.toFinset

def implementation (s0 s1: String) : Bool :=
  chars_set s0 = chars_set s1

def problem_spec
-- function signature
(impl: String → String → Bool)
-- inputs
(s0 s1: String) :=
-- spec
let spec (res: Bool) :=
  res ↔ (∀ c : Char, c ∈ s0.toList ↔ c ∈ s1.toList)
-- program terminates
∃ result, impl s0 s1 = result ∧
-- return value satisfies spec
spec result
-- if result then spec else ¬spec

-- LLM HELPER
lemma chars_set_mem_iff (s : String) (c : Char) : c ∈ chars_set s ↔ c ∈ s.toList := by
  simp [chars_set, List.mem_toFinset]

theorem correctness
(s0 s1: String)
: problem_spec implementation s0 s1  := by
  simp [problem_spec, implementation]
  use chars_set s0 = chars_set s1
  constructor
  · rfl
  · constructor
    · intro h c
      rw [← chars_set_mem_iff, ← chars_set_mem_iff]
      rw [h]
    · intro h
      ext c
      rw [chars_set_mem_iff, chars_set_mem_iff]
      exact h c

-- #test implementation 'eabcdzzzz' 'dddzzzzzzzddeddabc' = true
-- #test implementation 'abcd' 'dddddddabc' = true
-- #test implementation 'dddddddabc' 'abcd' = true
-- #test implementation 'eabcd' 'dddddddabc' = false
-- #test implementation 'abcd' 'dddddddabce' = false
-- #test implementation 'eabcdzzzz' 'dddzzzzzzzddddabc' = false