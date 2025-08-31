/- 
function_signature: "def int_to_mini_roman(num: Nat) -> String"
docstring: |
    Given a positive integer, obtain its roman numeral equivalent as a string,
    and return it in lowercase.
    Restrictions: 1 <= num <= 1000
test_cases:
  - input: 19
    expected_output: xix
  - input: 152
    expected_output: clii
  - input: 426
    expected_output: cdxxvi
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (num: Nat) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: Nat → String)
-- inputs
(num: Nat) :=
-- spec
let spec (result: String) :=
1 ≤ num ∧ num ≤ 1000 ∧ (result.data.all (fun c => c.isLower)) →
isValidRoman result ∧ romanToDecimal result = num
-- program terminates
∃ result, impl num = result ∧
-- return value satisfies spec
spec result

theorem correctness
(num: Nat)
: problem_spec implementation num :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 19 = "xix"
-- #test implementation 152 = "clii"
-- #test implementation 426 = "cdxxvi"