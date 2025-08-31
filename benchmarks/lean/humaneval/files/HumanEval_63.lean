/- 
function_signature: "def fibfib(n: int)"
docstring: |
    The FibFib number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows:
    fibfib(0) == 0
    fibfib(1) == 0
    fibfib(2) == 1
    fibfib(n) == fibfib(n-1) + fibfib(n-2) + fibfib(n-3).
    Please write a function to efficiently compute the n-th element of the fibfib number sequence.
Note(Meghana): While the specification asks for an efficient computation of fibfib, we cannot enforce this constraint currently.
test_cases:
  - input: 1
    output: 0
  - input: 5
    output: 4
  - input: 8
    output: 24
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
fibonacci_non_computable_3 n result
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

-- #test implementation 1 = 0
-- #test implementation 5 = 4
-- #test implementation 8 = 24