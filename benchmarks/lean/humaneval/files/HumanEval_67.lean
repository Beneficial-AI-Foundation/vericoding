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
def implementation (string: String) (n: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>

-- #test implementation "5 apples and 6 oranges" 19 = 8
-- #test implementation "0 apples and 1 oranges" 3 = 2
-- #test implementation "2 apples and 3 oranges" 100 = 95
-- #test implementation "100 apples and 1 oranges" 120 = 19