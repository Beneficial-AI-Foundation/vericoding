/- 
function_signature: "def is_multiply_prime(a: int) -> bool"
docstring: |
    Write a function that returns true if the given number is the multiplication of 3 prime numbers
    and false otherwise. Knowing that (a) is less then 100.
test_cases:
  - input: 30
    expected_output: True
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (a: Int) : Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: Int → Bool)
-- inputs
(a: Int) :=
-- spec
let spec (result: Bool) :=
  (a < 100) →
    result ↔ exists a' b c, (Nat.Prime a') ∧ (Nat.Prime b) ∧ (Nat.Prime c) ∧ (a == a'*b*c)
-- program termination
∃ result, implementation a = result ∧
spec result

theorem correctness
(a: Int)
: problem_spec implementation a
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 5 = False
-- #test implementation 30 = True
-- #test implementation 8 = True
-- #test implementation 10 = False
-- #test implementation 125 = True
-- #test implementation (3 * 5 * 7) = True
-- #test implementation (3 * 6 * 7) = False
-- #test implementation (9 * 9 * 9) = False
-- #test implementation (11 * 9 * 9) = False
-- #test implementation (11*13*7) = True