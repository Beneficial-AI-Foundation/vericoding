import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (a: Int) : Bool :=
  sorry

def problem_spec
-- function signature
(implementation: Int → Bool)
-- inputs
(a: Int) :=
-- spec
let spec (result: Bool) :=
  (a < 100) →
    result ↔ exists a' b c, (Nat.Prime a') ∧ (Nat.Prime b) ∧ (Nat.Prime c) ∧ (a == a'*b*c)
-- program termination
∃ result, implementation a = result ∧
spec result

theorem correctness
(a: Int)
: problem_spec implementation a
:= by
  sorry

-- #test implementation 5 = False
-- #test implementation 30 = True
-- #test implementation 8 = True
-- #test implementation 10 = False
-- #test implementation 125 = True
-- #test implementation (3 * 5 * 7) = True
-- #test implementation (3 * 6 * 7) = False
-- #test implementation (9 * 9 * 9) = False
-- #test implementation (11 * 9 * 9) = False
-- #test implementation (11*13*7) = True