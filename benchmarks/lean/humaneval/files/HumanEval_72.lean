/- 
function_signature: "def will_it_fly(q: List[int], w: int) -> bool"
docstring: |
    Write a function that returns True if the object q will fly, and False otherwise.
    The object q will fly if it's balanced (it is a palindromic list) and the sum of its elements is
    less than or equal the maximum possible weight w.
test_cases:
  - input: ([1, 2], 5)
    expected_output: False
  - input: ([3, 2, 3], 1)
    expected_output: False
  - input: ([3, 2, 3], 9)
    expected_output: True
  - input: ([3], 5)
    expected_output: True
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (q: List Int) (w: Int) : Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List Int → Int → Bool)
-- inputs
(q: List Int) (w: Int) :=
-- spec
let spec (result : Bool) :=
  (result → (List.Palindrome q)) ∧
  (result → (List.sum q ≤ w)) ∧
  (¬(List.Palindrome q) → ¬ result) ∧
  (¬(List.sum q ≤ w) → ¬ result)
-- program termination
∃ result, implementation q w = result ∧
spec result

theorem correctness
(q: List Int) (w: Int)
: problem_spec implementation q w
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [3, 2, 3] 9 = True
-- #test implementation [1, 2] 5 = False
-- #test implementation [3] 5 = True
-- #test implementation [3, 2, 3] 1 = False
-- #test implementation [1, 2, 3] 6 = False
-- #test implementation [5] 5 = True