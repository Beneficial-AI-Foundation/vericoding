/- 
function_signature: "def smallest_change(arr: List[int]) -> int"
docstring: |
    Given an array arr of integers, find the minimum number of elements that
    need to be changed to make the array palindromic. A palindromic array is an array that
    is read the same backwards and forwards. In one change, you can change one element to any other element.
test_cases:
  - input: [1,2,3,5,4,7,9,6]
    expected_output: 4
  - input: [1, 2, 3, 4, 3, 2, 2]
    expected_output: 1
  - input: [1, 2, 3, 2, 1]
    expected_output: 0
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (arr: List Int) : Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(arr: List Int) :=
-- spec
let spec (result : Int) :=
  let swaps_done (arr1: List Int) (arr2: List Int) :=
    ((List.finRange (arr1.length)).filter (fun idx => arr1[idx]? ≠ arr2[idx]?)).length/2
  ∀ palin_perm, (List.Perm arr palin_perm) ∧ (List.Palindrome palin_perm) →
    result ≤ (swaps_done arr palin_perm)
-- program termination
∃ result, implementation arr = result ∧
spec result

theorem correctness
(arr: List Int)
: problem_spec implementation arr
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [1,2,3,5,4,7,9,6] = 4
-- #test implementation [1, 2, 3, 4, 3, 2, 2] = 1
-- #test implementation [1, 4, 2] = 1
-- #test implementation [1, 4, 4, 2] = 1
-- #test implementation [1, 2, 3, 2, 1] = 0
-- #test implementation [3, 1, 1, 3] = 0
-- #test implementation [1] = 0
-- #test implementation [0, 1] = 1