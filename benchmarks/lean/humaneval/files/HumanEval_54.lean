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

def implementation (s0 s1: String) : Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

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

theorem correctness
(s0 s1: String)
: problem_spec implementation s0 s1  :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 'eabcdzzzz' 'dddzzzzzzzddeddabc' = true
-- #test implementation 'abcd' 'dddddddabc' = true
-- #test implementation 'dddddddabc' 'abcd' = true
-- #test implementation 'eabcd' 'dddddddabc' = false
-- #test implementation 'abcd' 'dddddddabce' = false
-- #test implementation 'eabcdzzzz' 'dddzzzzzzzddddabc' = false