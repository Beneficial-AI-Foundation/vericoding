import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (numbers: List Int) : (Int × Int) :=
  sorry

def problem_spec
-- function signature
(implementation: List Int → (Int × Int))
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: (Int × Int)) :=
let (sum, prod) := result;
(numbers = [] → sum = 0 ∧ prod = 1) ∧
(numbers ≠ [] →
(let (sum_tail, prod_tail) := implementation numbers.tail;
sum - sum_tail = numbers[0]! ∧
sum_tail * prod_tail + prod = sum * prod_tail));
-- program termination
∃ result, implementation numbers = result ∧
spec result

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  sorry

-- #test implementation [] = (0, 1)
-- #test implementation [1, 2, 3, 4] = (10, 24)