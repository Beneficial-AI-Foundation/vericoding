-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (l: List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(l: List Int) :=
-- spec
let spec (result: Int) :=
  l.length > 0 →
  ((∀ i, i < l.length → l[i]! ≤ result) ∧
  (∃ i, i < l.length ∧ l[i]! = result));
-- program termination
∃ result, implementation l = result ∧
spec result

theorem correctness
(l: List Int)
: problem_spec implementation l
:= by
  sorry
-- </vc-theorems>