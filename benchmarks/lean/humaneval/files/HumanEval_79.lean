/- 
function_signature: "def decimal_to_binary(decimal: nat) -> string"
docstring: |
    You will be given a number in decimal form and your task is to convert it to
    binary format. The function should return a string, with each character representing a binary
    number. Each character in the string will be '0' or '1'.

    There will be an extra couple of characters 'db' at the beginning and at the end of the string.
    The extra characters are there to help with the format.
test_cases:
  - input: 15
    expected_output: "db1111db"
  - input: 32
    expected_output: "db100000db"
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (decimal: Nat) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: Nat → String)
-- inputs
(decimal: Nat) :=
-- spec
let spec (result: String) :=
  4 < result.length ∧
  result.drop (result.length - 2) = "db" ∧
  result.take 2 = "db" ∧
  let resultTrimmed := (result.toList.drop 2).dropLast.dropLast.map (fun c => c.toNat - '0'.toNat)
  decimal = Nat.ofDigits 2 resultTrimmed.reverse
-- program termination
∃ result, implementation decimal = result ∧
spec result

theorem correctness
(decimal: Nat)
: problem_spec implementation decimal
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 0 = "db0db"
-- #test implementation 32 = "db100000db"
-- #test implementation 103 = "db1100111db"
-- #test implementation 15 = "db1111db"