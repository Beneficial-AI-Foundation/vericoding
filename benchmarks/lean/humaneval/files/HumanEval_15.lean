/- 
function_signature: "def string_sequence(n: int) -> str"
docstring: |
    Return a string containing space-delimited numbers starting from 0 upto n inclusive.
test_cases:
  - input: 0
    expected_output: "0"
  - input: 5
    expected_output: "0 1 2 3 4 5"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

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
let spec (result: String) :=
let result_nums := result.splitOn " ";
result_nums.length = n + 1 ∧
∀ i, i < n + 1 → result_nums[i]! = i.repr;
-- program termination
∃ result, implementation n = result ∧
spec result

theorem correctness
(n: Nat)
: problem_spec implementation n
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 0 = "0"
-- #test implementation 5 = "0 1 2 3 4 5"