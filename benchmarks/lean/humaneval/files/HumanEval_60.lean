/- 
function_signature: "def sum_to_n(n: Nat) -> Nat"
docstring: |
    sum_to_n is a function that sums numbers from 1 to n.
test_cases:
  - input: 30
    expected_output: 465
  - input: 100
    expected_output: 4950
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (n: Nat) : Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n : Nat) :=
-- spec
let spec (result: Nat) :=
  0 < n →
  (result = 1 ↔ n = 1) ∧
  (∀ i, implementation (i + 1) - (implementation i) = i + 1)
-- program termination
∃ result, implementation n = result ∧
spec result

theorem correctness
(n: Nat)
: problem_spec implementation n
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 30 = 465
-- #test implementation 100 = 5050
-- #test implementation 5 = 15
-- #test implementation 10 = 55
-- #test implementation 1 = 1