import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

/--
name: fibonacci_non_computable_3
use: |
  Non-computable definition to check if a number is a Fibonacci number such that
  fib(n) = fib(n - 1) + fib(n - 2) + fib(n - 3).
problems:
  - 63
-/
inductive fibonacci_non_computable_3 : ℕ → ℕ → Prop
| base0 : fibonacci_non_computable_3 0 0
| base1 : fibonacci_non_computable_3 1 0
| base2 : fibonacci_non_computable_3 2 1
| step : ∀ n f₁ f₂ f₃, fibonacci_non_computable_3 n f₁ →
fibonacci_non_computable_3 (n + 1) f₂ →
fibonacci_non_computable_3 (n + 2) f₃ →
fibonacci_non_computable_3 (n + 3) (f₁ + f₂ + f₃)

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def fibfib : Nat → Nat
| 0 => 0
| 1 => 0
| 2 => 1
| n + 3 => fibfib n + fibfib (n + 1) + fibfib (n + 2)

def implementation (n: Nat) : Nat :=
  fibfib n

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

-- LLM HELPER
lemma fibfib_satisfies_spec (n : Nat) : fibonacci_non_computable_3 n (fibfib n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases' n with n
    · exact fibonacci_non_computable_3.base0
    · cases' n with n
      · exact fibonacci_non_computable_3.base1
      · cases' n with n
        · exact fibonacci_non_computable_3.base2
        · have h1 : n < n + 1 + 1 + 1 := by omega
          have h2 : n + 1 < n + 1 + 1 + 1 := by omega
          have h3 : n + 2 < n + 1 + 1 + 1 := by omega
          have ih1 := ih n h1
          have ih2 := ih (n + 1) h2  
          have ih3 := ih (n + 2) h3
          rw [fibfib]
          exact fibonacci_non_computable_3.step n (fibfib n) (fibfib (n + 1)) (fibfib (n + 2)) ih1 ih2 ih3

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec implementation
  use fibfib n
  constructor
  · rfl
  · exact fibfib_satisfies_spec n

-- #test implementation 1 = 0
-- #test implementation 5 = 4
-- #test implementation 8 = 24