import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (n: Nat): Bool :=
  sorry

def problem_spec
-- function signature
(implementation: Nat → Bool)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Bool) :=
  result ↔ ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0);
-- program termination
∃ result,
  implementation n = result ∧
  spec result

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  sorry

-- #test implementation 6 = false
-- #test implementation 101 = true
-- #test implementation 11 = true
-- #test implementation 13441 = true
-- #test implementation 61 = true
-- #test implementation 4 = false
-- #test implementation 1 = false