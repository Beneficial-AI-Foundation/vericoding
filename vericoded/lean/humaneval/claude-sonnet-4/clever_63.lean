-- <vc-preamble>
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
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Function to compute the nth value in the sequence
def fib3_aux : ℕ → ℕ
| 0 => 0
| 1 => 0  
| 2 => 1
| n + 3 => fib3_aux n + fib3_aux (n + 1) + fib3_aux (n + 2)

-- LLM HELPER: Lemma showing our function satisfies the relation
lemma fib3_aux_correct (n : ℕ) : fibonacci_non_computable_3 n (fib3_aux n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact fibonacci_non_computable_3.base0
    | succ n =>
      cases n with
      | zero => exact fibonacci_non_computable_3.base1
      | succ n =>
        cases n with
        | zero => exact fibonacci_non_computable_3.base2
        | succ n =>
          have h1 : n < n + 3 := by omega
          have h2 : n + 1 < n + 3 := by omega
          have h3 : n + 2 < n + 3 := by omega
          exact fibonacci_non_computable_3.step n (fib3_aux n) (fib3_aux (n + 1)) (fib3_aux (n + 2)) (ih n h1) (ih (n + 1) h2) (ih (n + 2) h3)
-- </vc-helpers>

-- <vc-definitions>
def implementation (n: Nat) : Nat :=
  fib3_aux n
-- </vc-definitions>

-- <vc-theorems>
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
:= by
  unfold problem_spec
  use fib3_aux n
  constructor
  · rfl
  · exact fib3_aux_correct n
-- </vc-theorems>

-- #test implementation 1 = 0
-- #test implementation 5 = 4
-- #test implementation 8 = 24