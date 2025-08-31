/- 
function_signature: "def solve(n: int) -> str"
docstring: |
    Given a positive integer N, return the total sum of its digits in binary.
test_cases:
  - input: 1000
    output: "1"
  - input: 150
    output: "110"
  - input: 147
    output: "1100"
Note: The spec formalization takes the result, makes it a list of 0/1s and then reverse it and uses Nat.ofDigits. The reversal is because ofDigits expects little-endian order.
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (n: Nat) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: Nat → String)
-- inputs
(n: Nat) :=
-- spec
let spec (result : String) :=
  0 < n →
  result.all (fun c => c = '0' ∨ c = '1') →
  Nat.ofDigits 2 (result.data.map (fun c => if c = '0' then 0 else 1)).reverse = (Nat.digits 10 n).sum
-- program termination
∃ result,
  implementation n = result ∧
  spec result

theorem correctness
(n: Nat)
: problem_spec implementation n
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 1000 = "1"
-- #test implementation 150 = "110"
-- #test implementation 147 = "1100"