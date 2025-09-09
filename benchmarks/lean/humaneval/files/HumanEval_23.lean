import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (string: String): Nat :=
  sorry

def problem_spec
-- function signature
(implementation: String → Nat)
-- inputs
(string: String) :=
-- spec
let spec (result: Nat) :=
-- every character in the string is counted once
result = 0 ↔ string.isEmpty ∧
(0 < result → result - 1 = implementation (string.drop 1))
-- program termination
∃ result, implementation string = result ∧
spec result

theorem correctness
(string: String)
: problem_spec implementation string
:= by
  sorry

-- #test implementation "" = 0
-- #test implementation "abc" = 3