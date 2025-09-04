/- 
function_signature: "def by_length(arr: List[int]) -> List[string]"
docstring: |
    Given an array of integers, sort the integers that are between 1 and 9 inclusive,
    reverse the resulting array, and then replace each digit by its corresponding name from
    "One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine".
test_cases:
  - input: [2, 1, 1, 4, 5, 8, 2, 3]
    expected_output: ["Eight", "Five", "Four", "Three", "Two", "Two", "One", "One"]
  - input: []
    expected_output: []
  - input: [1, -1 , 55]
    expected_output: ['One']
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (arr: List Int) : List String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List Int → List String)
-- inputs
(arr: List Int) :=
-- spec
let spec (result: List String) :=
  let digits: List String := ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"];
  (forall s: String, (s ∈ result → s ∈ digits)) ∧
  (arr.length ≥ result.length) ∧
  (forall x: Nat, ((x: Int) ∈ arr ∧ 1 ≤ x ∧ x ≤ 9) → (digits[x-1]! ∈ result)) ∧
  (List.Sorted Int.le (List.map (fun (s: String) => (List.idxOf s digits) + 1) result).reverse)
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

-- #test implementation [2, 1, 1, 4, 5, 8, 2, 3] = ["Eight", "Five", "Four", "Three", "Two", "Two", "One", "One"]
-- #test implementation [] = []
-- #test implementation [1, -1 , 55] = ["One"]
-- #test implementation [1, -1, 3, 2] = ["Three", "Two", "One"]
-- #test implementation [9, 4, 8] = ["Nine", "Eight", "Four"]