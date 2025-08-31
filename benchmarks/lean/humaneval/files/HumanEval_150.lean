/- 
function_signature: "def x_or_y(int n, int x, int y) -> int"
docstring: |
    A simple program which should return the value of x if n is
    a prime number and should return the value of y otherwise.
test_cases:
  - input: [7, 34, 12]
    expected_output: 34
  - input: [15, 8, 5]
    expected_output: 5
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (n x y: Int) : Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: Int → Int → Int → Int)
-- inputs
(n x y: Int) :=
-- spec
let spec (result: Int) :=
(result = x ↔ Nat.Prime n.toNat) ∧
(result = y ↔ (¬ Nat.Prime n.toNat ∨ n ≤ 1))
-- program terminates
∃ result, impl n x y = result ∧
-- return value satisfies spec
spec result

theorem correctness
(n x y: Int)
: problem_spec implementation n x y :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 7 34 12 = 34
-- #test implementation 15 8 5 = 5