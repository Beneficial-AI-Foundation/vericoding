import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (a b c: Nat) : List Nat :=
  sorry

def problem_spec
-- function signature
(impl: Nat → Nat → Nat → List Nat)
-- inputs
(number need remaining: Nat) :=
-- spec
let spec (result: List Nat) :=
number ≤ 1000 → need ≤ 1000 → remaining ≤ 1000 →
result.length = 2 ∧
(need ≤ remaining → result[0]! - need = number ∧
need = remaining - result[1]!) ∧
(remaining < need → result[0]! - remaining = number ∧
result[1]! = 0);
-- program terminates
∃ result, impl number need remaining = result ∧
-- return value satisfies spec
spec result

theorem correctness
(a b c: Nat)
: problem_spec implementation a b c := by
  sorry

-- #test implementation 5 6 10 = [11, 4]
-- #test implementation 4 8 9 = [12, 1]
-- #test implementation 1 10 10 = [11, 0]
-- #test implementation 2 11 5 = [7, 0]