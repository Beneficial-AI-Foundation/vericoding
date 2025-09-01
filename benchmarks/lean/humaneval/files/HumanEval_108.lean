/- 
function_signature: "def count_nums(arr: List[int]) -> int"
docstring: |
    Write a function count_nums which takes an array of integers and returns
    the number of elements which has a sum of digits > 0.
    If a number is negative, then its first signed digit will be negative:
    e.g. -123 has signed digits -1, 2, and 3.
test_cases:
  - input: []
    expected_output: 0
  - input: [-1, 11, -11]
    expected_output: 1
  - input: [1, 1, 2]
    expected_output: 3
-/

import Imports.AllImports

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
let spec (result: Int) :=
  let dig_sum (x: Int): Int :=
    let digs := x.natAbs.digits 10;
    if x >= 0 then
      (List.map (fun t => (t: Int)) digs).sum
    else
      (List.map (fun t => (t: Int)) (digs.drop 1)).sum - (digs[0]! : Int);
  (arr = [] → result = 0) ∧
  (arr ≠ [] → 0 < (dig_sum arr[0]!) → result = 1 + implementation (arr.drop 1)) ∧
  (arr ≠ [] → (dig_sum arr[0]!) ≤ 0 → result = implementation (arr.drop 1));
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

-- #test implementation [] = 0
-- #test implementation [-1, -2, 0] = 0
-- #test implementation [1, 1, 2, -2, 3, 4, 5] = 6
-- #test implementation [1, 6, 9, -6, 0, 1, 5] = 5
-- #test implementation [1, 100, 98, -7, 1, -1] = 4
-- #test implementation [12, 23, 34, -45, -56, 0] = 5
-- #test implementation [-0, 1^0] = 1
-- #test implementation [1] = 1