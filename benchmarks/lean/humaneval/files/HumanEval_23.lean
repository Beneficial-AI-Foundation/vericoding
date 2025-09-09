import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

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

-- <vc-helpers>

-- </vc-helpers>

-- <vc-description>
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
-- </vc-description>

-- <vc-spec>
def implementation (string: String): Nat :=
-- </vc-spec>
-- <vc-code>
sorry
-- </vc-code>

-- <vc-theorem>
theorem correctness
(string: String)
: problem_spec implementation string
:=
-- </vc-theorem>
-- <vc-proof>
by
  sorry
-- </vc-proof>

-- #test implementation "" = 0
-- #test implementation "abc" = 3