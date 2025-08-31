/- 
function_signature: "def derivative(xs: List Int) -> List Int"
docstring: |
    xs represent coefficients of a polynomial.
    xs[0] + xs[1] * x + xs[2] * x^2 + ....
     Return derivative of this polynomial in the same form.
test_cases:
  - input: [3, 1, 2, 4, 5]
    expected_output: [1, 4, 12, 20]
  - input: [1, 2, 3]
    expected_output: [2, 6]
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (xs: List Int) : List Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

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
: problem_spec implementation xs :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [3, 1, 2, 4, 5] : List Int = [1, 4, 12, 20]
-- #test implementation [1, 2, 3] : List Int = [2, 6]