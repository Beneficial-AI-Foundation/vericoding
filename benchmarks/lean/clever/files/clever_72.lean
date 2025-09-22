-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (q: List Int) (w: Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: List Int → Int → Bool)
-- inputs
(q: List Int) (w: Int) :=
-- spec
let spec (result : Bool) :=
  (result → (List.Palindrome q)) ∧
  (result → (List.sum q ≤ w)) ∧
  (¬(List.Palindrome q) → ¬ result) ∧
  (¬(List.sum q ≤ w) → ¬ result)
-- program termination
∃ result, implementation q w = result ∧
spec result

theorem correctness
(q: List Int) (w: Int)
: problem_spec implementation q w
:= by
  sorry
-- </vc-theorems>