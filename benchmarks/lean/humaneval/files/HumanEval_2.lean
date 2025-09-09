import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (number: Rat) : Rat :=
  sorry

def problem_spec
-- function signature
(impl: Rat → Rat)
-- inputs
(number: Rat) :=
-- spec
let spec (res) :=
0 ≤ res ∧
res < 1 ∧
number.floor + res = number;
number > 0 →
-- program terminates
(∃ result, impl number = result ∧
-- return value satisfies spec
spec result)

theorem correctness
(number: Rat)
: problem_spec implementation number := by
  sorry

-- #test implementation 3.5 = 0.5