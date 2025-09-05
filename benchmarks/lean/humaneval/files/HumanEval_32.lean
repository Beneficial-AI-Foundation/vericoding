/- 
function_signature: "def find_zero(xs: list)"
docstring: |
    xs are coefficients of a polynomial.
    find_zero find x such that poly(x) = 0.
    find_zero returns only only zero point, even if there are many.
    Moreover, find_zero only takes list xs having even number of coefficients
    and largest non zero coefficient as it guarantees a solution.
    Note(George): This problem has been modified from the original HumanEval spec because of Real is not a computable type, but a zero does not necessarily exist over the rationals.
test_cases:
  - input: [1, 2]
    output: -0.5
  - input: [-6, 11, -6, 1]
    output: 1.0
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (xs: List Rat) : Rat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List Rat → Rat)
-- inputs
(xs: List Rat) :=
-- spec
let spec (result: Rat) :=
  let eps := (1: Rat) / 1000000;
  xs.length ≥ 1 → xs.length % 2 = 0 →
  ∀ poly : Polynomial Rat,
    poly.degree = some (xs.length - 1) →
    (∀ i, i ≤ xs.length - 1 → poly.coeff i = xs[i]!) →
    |poly.eval result| ≤ eps;
-- program termination
∃ result,
  implementation xs = result ∧
  spec result

theorem correctness
(xs: List Rat)
: problem_spec implementation xs
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [1, 2] = -0.5
-- #test implementation [-6, 11, -6, 1] = 1.0