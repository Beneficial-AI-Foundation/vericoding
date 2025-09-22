-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (string: String): Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>