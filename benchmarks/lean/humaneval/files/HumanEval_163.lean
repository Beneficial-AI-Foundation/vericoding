/- 
function_signature: "def generate_integers(a : Nat, b : Nat) -> List Nat"
docstring: |
    Given two positive integers a and b, return the even digits between a
    and b, in ascending order.
test_cases:
  - input: [2, 8]
    expected_output: [2, 4, 6, 8]
  - input: [8, 2]
    expected_output: [2, 4, 6, 8]
  - input: [10, 14]
    expected_output: [10, 12, 14]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (a b: Nat) : List Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: Nat → Nat → List Nat)
-- inputs
(a b : Nat) :=
let isAscendingBy2 (r : List Nat) :=
∀ i, i < r.length - 1 → r[i+1]! - r[i]! = 2
-- spec
let spec (result: List Nat) :=
result.all (fun n => n % 2 = 0) ∧ isAscendingBy2 result ∧
1 < result.length ∧
let min_a_b := min a b;
let max_a_b := max a b;
if min_a_b = max_a_b ∧ (min_a_b % 2 = 1)
then result = []
else ((result[0]! = if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)) ∧
(result[result.length-1]! = if 2 ∣ max_a_b then max_a_b else max_a_b - 1))
-- program terminates
∃ result, impl a b = result ∧
-- return value satisfies spec
spec result

theorem correctness
(a b: Nat)
: problem_spec implementation a b :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 2 8 = [2, 4, 6, 8]
-- #test implementation 8 2 = [2, 4, 6, 8]
-- #test implementation 10 14 = [10, 12, 14]