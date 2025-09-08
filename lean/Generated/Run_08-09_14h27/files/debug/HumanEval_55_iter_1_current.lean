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
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => implementation n + implementation (n + 1)

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

-- LLM HELPER
theorem implementation_correct : ∀ n, fibonacci_non_computable n (implementation n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases' n with n
    · exact fibonacci_non_computable.base0
    · cases' n with n
      · exact fibonacci_non_computable.base1  
      · rw [implementation]
        apply fibonacci_non_computable.step
        · exact ih n (Nat.lt_add_of_pos_right (by norm_num : 0 < 2))
        · exact ih (n + 1) (Nat.lt_add_of_pos_right (by norm_num : 0 < 1))

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  use implementation n
  constructor
  · rfl
  · exact implementation_correct n

-- #test implementation 10 = 55
-- #test implementation 1 = 1
-- #test implementation 8 = 21