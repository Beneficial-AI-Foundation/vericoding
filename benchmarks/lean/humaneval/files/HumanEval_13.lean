import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (a b: Int) : Int :=
  sorry

def problem_spec
-- function signature
(implementation: Int → Int → Int)
-- inputs
(a b: Int) :=
-- spec
let spec (result: Int) :=
(result ∣ a) ∧
(result ∣ b) ∧
(∀ (d': Int),
(d' > 0) → (d' ∣ a) → (d' ∣ b) →
d' ≤ result);
-- program termination
∃ result, implementation a b = result ∧
spec result

theorem correctness
(a b: Int)
: problem_spec implementation a b
:= by
  sorry

-- #test implementation 25 15 = 5
-- #test implementation 3 5 = 1