/- 
function_signature: "def is_simple_power(x: int, n: int) -> bool"
docstring: |
    Your task is to write a function that returns true if a number x is a simple
    power of n and false in other cases. x is a simple power of n if n**int=x
test_cases:
  - input: (1, 4)
    expected_output: True
  - input: (2, 2)
    expected_output: True
  - input: (8, 2)
    expected_output: True
  - input: (3, 2)
    expected_output: False
  - input: (3, 1)
    expected_output: False
  - input: (5, 3)
    expected_output: False
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (x: Int) (n: Int) : Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: Int → Int → Bool)
-- inputs
(x: Int) (n: Int) :=
-- spec
let spec (result: Bool) :=
  result ↔ exists k: Nat, x = n^k
-- program termination
∃ result, implementation x n = result ∧
spec result

theorem correctness
(x: Int) (n: Int)
: problem_spec implementation x n
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 16 2 = True
-- #test implementation 143214 16 = False
-- #test implementation 4 2 = True
-- #test implementation 9 3 = True
-- #test implementation 16 4 = True
-- #test implementation 24 2 = False
-- #test implementation 128 4 = False
-- #test implementation 12 6 = False
-- #test implementation 1 1 = True
-- #test implementation 1 12 = True