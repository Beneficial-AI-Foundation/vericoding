-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

noncomputable def check_derivative : List ℤ → List ℤ
  | []       => []
  | (x::rest)  => (Polynomial.eval 1 (Polynomial.derivative (Polynomial.C x * Polynomial.X ^ rest.length))) :: (check_derivative rest)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (xs: List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(impl: List Int → List Int)
-- inputs
(xs: List Int) :=
-- spec
let spec (result: List Int) :=
  result.length = xs.length - 1 ∧
  result = (check_derivative xs.reverse).reverse
-- program terminates
∃ result, impl xs = result ∧
-- return value satisfies spec
spec result

theorem correctness
(xs: List Int)
: problem_spec implementation xs := by
  sorry
-- </vc-theorems>