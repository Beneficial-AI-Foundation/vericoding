/- 
function_signature: "def can_arrange(arr: List[int]) -> int"
docstring: |
    Create a function which returns the largest index of an element which
    is not greater than or equal to the element immediately preceding it. If
    no such element exists then return -1. The given array will not contain
    duplicate values.
test_cases:
  - input: [1, 2, 4, 3, 5]
    expected_output: 3
  - input: [1, 2, 3]
    expected_output: -1
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
(impl: List Int → Int)
-- inputs
(arr: List Int) :=
-- spec
let spec (result: Int) :=
  ¬arr.any (fun x => 1 < arr.count x) →
  (arr.length = 0 ∨ arr.length = 1 → result = -1) ∧
  (1 < arr.length →
    let last := arr.length-1;
    let i := if arr[last]! < arr[last-1]! then Int.ofNat last else -1;
    result = max (impl (arr.take last)) i);
-- program termination
∃ result, impl arr = result ∧
-- return value satisfies spec
spec result

theorem correctness
(arr: List Int)
: problem_spec implementation arr :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [1, 2, 4, 3, 5] = 3
-- #test implementation [1, 2, 3] = -1