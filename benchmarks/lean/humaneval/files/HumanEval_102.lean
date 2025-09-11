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
def implementation (x: Int) (y: Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: Int → Int → Int)
-- inputs
(x: Int) (y: Int) :=
-- spec
let spec (result: Int) :=
  (result = -1 ∨ (x ≤ result ∧ result ≤ y ∧ Even result)) ∧
  (result = -1 ∨ (forall i: Int, (x ≤ i ∧ i ≤ y ∧ Even i) → result ≥ i)) ∧
  (result = -1 ↔ (x > y ∨ (x == y ∧ Odd x ∧ Odd y)))
-- program termination
∃ result, implementation x y = result ∧
spec result

theorem correctness
(x: Int) (y: Int)
: problem_spec implementation x y
:= by
  sorry
-- </vc-theorems>

-- #test implementation 12 15 = 14
-- #test implementation 13 12 = -1
-- #test implementation 33 12354 = 12354
-- #test implementation 5234 5233 = -1
-- #test implementation 6 29 = 28
-- #test implementation 27 10 = (-1)
-- #test implementation 7 7 = -1
-- #test implementation 546 546 = 546