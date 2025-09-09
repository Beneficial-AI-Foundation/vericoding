import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (string: String) (n: Nat) : Nat :=
  sorry

def problem_spec
-- function signature
(implementation: String → Nat → Nat)
-- inputs
(string: String)
(n : Nat) :=
-- spec
let spec (result: Nat) :=
∃ x y : Nat, x + y = n - result
∧ (String.join [x.repr, " apples and ", y.repr, " oranges"] = string)
-- program termination
∃ result, implementation string n = result ∧
spec result

theorem correctness
(s: String) (n : Nat)
: problem_spec implementation s n
:= by
  sorry

-- #test implementation "5 apples and 6 oranges" 19 = 8
-- #test implementation "0 apples and 1 oranges" 3 = 2
-- #test implementation "2 apples and 3 oranges" 100 = 95
-- #test implementation "100 apples and 1 oranges" 120 = 19