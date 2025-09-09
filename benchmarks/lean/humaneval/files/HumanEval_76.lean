import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (x: Int) (n: Int) : Bool :=
  sorry

def problem_spec
-- function signature
(implementation: Int → Int → Bool)
-- inputs
(x: Int) (n: Int) :=
-- spec
let spec (result: Bool) :=
  result ↔ exists k: Nat, x = n^k
-- program termination
∃ result, implementation x n = result ∧
spec result

theorem correctness
(x: Int) (n: Int)
: problem_spec implementation x n
:= by
  sorry

-- #test implementation 16 2 = True
-- #test implementation 143214 16 = False
-- #test implementation 4 2 = True
-- #test implementation 9 3 = True
-- #test implementation 16 4 = True
-- #test implementation 24 2 = False
-- #test implementation 128 4 = False
-- #test implementation 12 6 = False
-- #test implementation 1 1 = True
-- #test implementation 1 12 = True