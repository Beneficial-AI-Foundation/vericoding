-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (a h: Rat) : Rat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: Rat → Rat -> Rat)
-- inputs
(a h: Rat) :=
-- spec
let spec (result: Rat) :=
  a = 0 → result = 0 ∧
  (a ≠ 0 → (2 * result) / a = h);
-- -- program termination
∃ result, implementation a h = result ∧
spec result

theorem correctness
(a h : Rat)
: problem_spec implementation a h
:= by
  sorry
-- </vc-theorems>