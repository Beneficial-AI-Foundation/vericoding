-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (numbers: List Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: List Int → Bool)
-- inputs
(numbers: List Int) :=
let sum_i_j (i j: Nat) : Bool :=
  numbers[i]! + numbers[j]! = 0;
let exists_zero := 2 ≤ numbers.length ∧ (∃ i j, i ≠ j ∧
 i < numbers.length ∧ j < numbers.length ∧
 sum_i_j i j)
-- spec
let spec (result: Bool) :=
result ↔ exists_zero
-- -- program termination
∃ result, implementation numbers = result ∧
spec result

theorem correctness
(numbers : List Int)
: problem_spec implementation numbers
:= by
  sorry
-- </vc-theorems>

-- #test implementation [1, 3, 5, 0] = false
-- #test implementation [1, 3, -2, 1] = false
-- #test implementation [1, 2, 3, 7] = false
-- #test implementation [2, 4, -5, 3, 5, 7] = true
-- #test implementation [1] = false