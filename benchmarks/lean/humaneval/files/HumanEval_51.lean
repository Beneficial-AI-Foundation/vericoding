/- 
function_signature: "def remove_vowels(string: str) -> string"
docstring: |
    remove_vowels is a function that takes string and returns string without vowels.
test_cases:
  - input: ""
    expected_output: ""
  - input: "abcdef\nghijklm"
    expected_output: "bcdf\nghjklm"
  - input: "abcdef"
    expected_output: "bcdf"
  - input: "aaaaa"
    expected_output: ""
  - input: "aaBAA"
    expected_output: "B"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (string: String) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(string: String) :=
let is_consonant (c: Char): Bool :=
  let vowels := "aeiouAEIOU"
  not (vowels.contains c);
-- spec
let spec (result: String) :=
result.all (λ c => is_consonant c) ∧ result.length ≤ string.length ∧
∀ c, result.contains c → string.contains c ∧
∀ c , string.contains c ∧ is_consonant c → (result.contains c);
-- program termination
∃ result, implementation string = result ∧
spec result

theorem correctness
(s: String)
: problem_spec implementation s
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "" = ""
-- #test implementation "cat" = "catac"
-- #test implementation "cata" = "catac"