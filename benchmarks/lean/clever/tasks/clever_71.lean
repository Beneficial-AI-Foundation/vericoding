-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (a: Rat) (b: Rat) (c: Rat): Rat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: Rat → Rat → Rat → Rat)
-- inputs
(a: Rat) (b: Rat) (c: Rat) :=
-- spec
let spec (result : Rat) :=
  let is_valid_triangle :=
    (a + b > c) ∧  (a + c > b) ∧ (b + c > a);
  let s :=
    (a + b + c) / 2;
  if is_valid_triangle then
    |result^2 - (s * (s-a) * (s-b) * (s-c))| ≤ ((1: Rat)/10000)
  else
    result = -1
-- program termination
∃ result, implementation a b c = result ∧
spec result

theorem correctness
(a: Rat) (b: Rat) (c: Rat)
: problem_spec implementation a b c
:= by
  sorry
-- </vc-theorems>