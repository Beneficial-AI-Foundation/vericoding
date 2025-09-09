import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

/--
name: is_palindrome
use: |
  Helper to check if a string is a palindrome.
problems:
  - 10
  - 48
-/
def is_palindrome
(s: String): Bool :=
s = s.toList.reverse.asString

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

-- <vc-helpers>

-- </vc-helpers>

-- <vc-description>
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
-- </vc-description>

-- <vc-spec>
def implementation (string: String) : Bool :=
-- </vc-spec>
-- <vc-code>
sorry
-- </vc-code>

-- <vc-theorem>
theorem correctness
(s: String)
: problem_spec implementation s
:=
-- </vc-theorem>
-- <vc-proof>
by
  sorry
-- </vc-proof>

-- #test implementation "" = true
-- #test implementation "aba" = true
-- #test implementation "aaaaa" = true
-- #test implementation "zbcd" = false