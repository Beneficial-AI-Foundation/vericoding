/- 
function_signature: "def fruit_distribution(string: str, Nat n) -> Nat"
docstring: |
    In this task, you will be given a string that represents a number of apples and oranges
    that are distributed in a basket of fruit this basket contains
    apples, oranges, and mango fruits. Given the string that represents the total number of
    the oranges and apples and an integer that represent the total number of the fruits
    in the basket return the number of the mango fruits in the basket.
test_cases:
  - input: ["5 apples and 6 oranges", 19]
    expected_output: 8
  - input: ["0 apples and 1 oranges", 3]
    expected_output: 2
  - input: ["2 apples and 3 oranges", 100]
    expected_output: 95
  - input: ["100 apples and 1 oranges", 120]
    expected_output: 19
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (string: String) (n: Nat) : Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: String → Nat → Nat)
-- inputs
(string: String)
(n : Nat) :=
-- spec
let spec (result: Nat) :=
∃ x y : Nat, x + y = n - result
∧ (String.join [x.repr, " apples and ", y.repr, " oranges"] = string)
-- program termination
∃ result, implementation string n = result ∧
spec result

theorem correctness
(s: String) (n : Nat)
: problem_spec implementation s n
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "5 apples and 6 oranges" 19 = 8
-- #test implementation "0 apples and 1 oranges" 3 = 2
-- #test implementation "2 apples and 3 oranges" 100 = 95
-- #test implementation "100 apples and 1 oranges" 120 = 19