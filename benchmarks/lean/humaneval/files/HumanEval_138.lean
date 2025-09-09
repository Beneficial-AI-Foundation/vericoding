import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (n: Int) : Bool :=
  sorry

def problem_spec
-- function signature
(impl: Int → Bool)
-- inputs
(n: Int) :=
-- spec
let spec (result: Bool) :=
  let sum_exists := ∃ a b c d : Nat,
    Even a ∧
    Even b ∧
    Even c ∧
    Even d ∧
    (a + b + c + d = n);
  result = true ↔ sum_exists
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

theorem correctness
(n: Int)
: problem_spec implementation n := by
  sorry

-- #test implementation 4 = false
-- #test implementation 6 = false
-- #test implementation 8 = true