-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (a b: Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>