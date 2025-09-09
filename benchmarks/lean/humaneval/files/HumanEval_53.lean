import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

def problem_spec
-- function signature
(impl: Int → Int → Int)
-- inputs
(x y: Int) :=
-- spec
let spec (res: Int) :=
  res - x - y = 0
-- program terminates
∃ result, impl x y = result ∧
-- return value satisfies spec
spec result
-- if result then spec else ¬spec

-- <vc-helpers>

-- </vc-helpers>

-- <vc-description>
/-
function_signature: "def add(x: Int, y: Int) -> Int"
docstring: Add two numbers x and y
test_cases:
  - input: [2, 3]
    expected_output: 5
  - input: [5, 7]
    expected_output: 12
-/
-- </vc-description>

-- <vc-spec>
def implementation (x y: Int) : Int :=
-- </vc-spec>
-- <vc-code>
sorry
-- </vc-code>

-- <vc-theorem>
theorem correctness
(x y: Int)
: problem_spec implementation x y  :=
-- </vc-theorem>
-- <vc-proof>
by
  sorry
-- </vc-proof>

-- #test implementation 2 3 = 5
-- #test implementation 5 7 = 12