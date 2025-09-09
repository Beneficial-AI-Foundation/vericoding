import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (n: Nat) : Nat :=
  sorry

def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n : Nat) :=
-- spec
let spec (result: Nat) :=
  0 < n →
  (result = 1 ↔ n = 1) ∧
  (∀ i, implementation (i + 1) - (implementation i) = i + 1)
-- program termination
∃ result, implementation n = result ∧
spec result

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  sorry

-- #test implementation 30 = 465
-- #test implementation 100 = 5050
-- #test implementation 5 = 15
-- #test implementation 10 = 55
-- #test implementation 1 = 1