/- 
function_signature: "def unique_digits(x: List[nat]) -> List[nat]"
docstring: |
    Given a list of positive integers x. return a sorted list of all
    elements that hasn't any even digit.

    Note: Returned list should be sorted in increasing order.
test_cases:
  - input: [15, 33, 1422, 1]
    expected_output: [1, 15, 33]
  - input: [152, 323, 1422, 10]
    expected_output: []
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (x: List Nat) : List Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(x: List Nat) :=
-- spec
let spec (result: List Nat) :=
  let has_even_digits(i: Nat): Bool :=
    (List.filter (fun d => Even d) (Nat.digits 10 i)).length > 0;
  (List.Sorted Nat.le result) ∧
  (forall i, i ∈ result ↔ (i ∈ x ∧ !(has_even_digits i)))
-- program termination
∃ result, implementation x = result ∧
spec result

theorem correctness
(x: List Nat)
: problem_spec implementation x
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [15, 33, 1422, 1] = [1, 15, 33]
-- #test implementation [152, 323, 1422, 10] = []
-- #test implementation [12345, 2033, 111, 151] = [111, 151]
-- #test implementation [135, 103, 31] = [31, 135]