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
def implementation (l: List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(l: List Int) :=
-- spec
let spec (result: List Int) :=
  (∀ x, x ∈ result ↔ x ∈ l ∧ result.count x = 1) ∧
  List.Sorted Int.le result
-- program termination
∃ result,
  implementation l = result ∧
  spec result

theorem correctness
(l: List Int)
: problem_spec implementation l
:= by
  sorry
-- </vc-theorems>

-- #test implementation [5, 3, 5, 2, 3, 3, 9, 0, 123] = [0, 2, 3, 5, 9, 123]