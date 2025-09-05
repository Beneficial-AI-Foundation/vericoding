/- 
function_signature: "def search(numbers: List[int]) -> int"
docstring: |
    You are given a non-empty list of positive integers. Return the greatest integer that is greater than
    zero, and has a frequency greater than or equal to the value of the integer itself.
    The frequency of an integer is the number of times it appears in the list.
    If no such a value exist, return -1.
test_cases:
  - input: [4, 1, 2, 2, 3, 1]
    expected_output: 2
  - input: [1, 2, 2, 3, 3, 3, 4, 4, 4]
    expected_output: 3
  - input: [5, 5, 4, 4, 4]
    expected_output: -1
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (numbers: List Int) : (Int) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: Int) :=
0 < numbers.length ∧ numbers.all (fun n => 0 < n) →
(result ≠ -1 ↔ ∃ i : Nat, i < numbers.length ∧
  numbers[i]! = result ∧ numbers[i]! > 0 ∧
  numbers[i]! ≤ (numbers.filter (fun x => x = numbers[i]!)).length ∧
  (¬∃ j : Nat, j < numbers.length ∧
  numbers[i]! < numbers[j]! ∧ numbers[j]! ≤ numbers.count numbers[j]!));
-- program termination
∃ result, implementation numbers = result ∧
spec result

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [4, 1, 2, 2, 3, 1] = 2
-- #test implementation [1, 2, 2, 3, 3, 4, 4, 4] = 3
-- #test implementation [5, 5, 4, 4, 4] = -1