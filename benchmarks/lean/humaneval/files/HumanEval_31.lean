/- 
function_signature: "def is_prime(n)"
docstring: |
    Return true if a given number is prime, and false otherwise.
test_cases:
  - input: 6
    output: False
  - input: 101
    output: True
  - input: 11
    output: True
  - input: 13441
    output: True
  - input: 61
    output: True
  - input: 4
    output: False
  - input: 1
    output: False
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (n: Nat): Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: Nat → Bool)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Bool) :=
  result ↔ ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0);
-- program termination
∃ result,
  implementation n = result ∧
  spec result

theorem correctness
(n: Nat)
: problem_spec implementation n
:=
-- <vc-proof>
  sorry
-- </vc-proof>

#test implementation 6 = false
#test implementation 101 = true
#test implementation 11 = true
#test implementation 13441 = true
#test implementation 61 = true
#test implementation 4 = false
#test implementation 1 = false