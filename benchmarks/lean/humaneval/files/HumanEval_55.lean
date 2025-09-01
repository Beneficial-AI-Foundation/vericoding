/- 
function_signature: "def fib(n: int) -> int"
docstring: |
    Return n-th Fibonacci number.
test_cases:
  - input: 10
    expected_output: 55
  - input: 1
    expected_output: 1
  - input: 8
    expected_output: 21
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
(n: Nat) :=
-- spec
let spec (result: Nat) :=
fibonacci_non_computable n result
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

-- #test implementation 10 = 55
-- #test implementation 1 = 1
-- #test implementation 8 = 21