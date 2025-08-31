/- 
function_signature: "def add(x: Int, y: Int) -> Int"
docstring: Add two numbers x and y
test_cases:
  - input: [2, 3]
    expected_output: 5
  - input: [5, 7]
    expected_output: 12
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (x y: Int) : Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

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

theorem correctness
(x y: Int)
: problem_spec implementation x y  :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 2 3 = 5
-- #test implementation 5 7 = 12