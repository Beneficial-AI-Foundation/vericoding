import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (x y: Int) : Int :=
  sorry

def problem_spec
-- function signature
(impl: Int → Int → Int)
-- inputs
(x y: Int) :=
-- spec
let spec (res: Int) :=
  res - x - y = 0
-- program terminates
∃ result, impl x y = result ∧
-- return value satisfies spec
spec result
-- if result then spec else ¬spec

theorem correctness
(x y: Int)
: problem_spec implementation x y  := by
  sorry

-- #test implementation 2 3 = 5
-- #test implementation 5 7 = 12