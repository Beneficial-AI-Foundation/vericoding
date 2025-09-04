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

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

/--
name: fibonacci_non_computable
use: |
  Non-computable definition to check if a number is a Fibonacci number.
problems:
  - 55
sample_problems:
  - 3
-/
inductive fibonacci_non_computable : ℕ → ℕ → Prop
| base0 : fibonacci_non_computable 0 0
| base1 : fibonacci_non_computable 1 1
| step  : ∀ n f₁ f₂, fibonacci_non_computable n f₁ →
fibonacci_non_computable (n + 1) f₂ →
fibonacci_non_computable (n + 2) (f₁ + f₂)

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