/- 
function_signature: "def iscube(a: int) -> bool"
docstring: |
    Write a function that takes an integer a and returns True if this integer is a cube of some integer number.
    Note: you may assume the input is always valid.
test_cases:
  - input: 1
    expected_output: True
  - input: 2
    expected_output: False
  - input: -1
    expected_output: True
  - input: 64
    expected_output: True
  - input: 0
    expected_output: True
  - input: 180
    expected_output: False
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (a: Int) : Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: Int → Bool)
-- inputs
(a: Int) :=
-- spec
let spec (result: Bool) :=
  result ↔ exists n: Int, a = n^3
-- program termination
∃ result, implementation a = result ∧
spec result

theorem correctness
(a: Int)
: problem_spec implementation a
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 1 = True
-- #test implementation 2 = False
-- #test implementation -1 = True
-- #test implementation 64 = True
-- #test implementation 180 = False
-- #test implementation 1000 = True
-- #test implementation 0 = True
-- #test implementation 1729 = False