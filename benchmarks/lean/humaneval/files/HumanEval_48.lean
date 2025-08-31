/- 
function_signature: "def is_palindrome(string: str) -> Bool"
docstring: |
    Checks if given string is a palindrome
test_cases:
  - input: ""
    expected_output: True
  - input: "aba"
    expected_output: True
  - input: "aaaaa"
    expected_output: "True"
  - input: "zbcd"
    expected_output: "False"
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (string: String) : Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: String → Bool)
-- inputs
(string: String) :=
-- spec
let spec (result: Bool) :=
result ↔ is_palindrome string
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

-- #test implementation "" = true
-- #test implementation "aba" = true
-- #test implementation "aaaaa" = true
-- #test implementation "zbcd" = false