/- 
function_signature: "def prime_fib(n: int)"
docstring: |
    prime_fib returns n-th prime Fibonacci number.
    Note(George): A proof of this problem requires the resolution of the open conjecture: there are infinitely many prime Fibonacci numbers.
test_cases:
  - input: 1
    output: 2
  - input: 2
    output: 3
  - input: 3
    output: 5
  - input: 4
    output: 13
  - input: 5
    output: 89
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
  n > 0 →
    (∃ i, Nat.fib i = result ∧ Nat.Prime result ∧
      (∃! S : Finset Nat, S.card = n - 1 ∧
      (∀ y ∈ S, (∃ k, y = Nat.fib k) ∧ y < result ∧ Nat.Prime y))
    )
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

-- NOTE we changed to #eval! instead of #test
-- because we can't use #test for implementation
-- without a proof of termination
#eval! implementation 1 = 2
#eval! implementation 2 = 3
#eval! implementation 3 = 5
#eval! implementation 4 = 13
#eval! implementation 5 = 89