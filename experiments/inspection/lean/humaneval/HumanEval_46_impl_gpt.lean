-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

/--
name: fibonacci_non_computable_4
use: |
  Non-computable definition to check if a number is a Fibonacci number such that
  fib(n) = fib(n - 1) + fib(n - 2) + fib(n - 3) + fib(n - 4).
problems:
  - 46
-/
inductive fibonacci_non_computable_4 : ℕ → ℕ → Prop
| base0 : fibonacci_non_computable_4 0 0
| base1 : fibonacci_non_computable_4 1 0
| base2 : fibonacci_non_computable_4 2 2
| base3 : fibonacci_non_computable_4 3 0
| step : ∀ n f₁ f₂ f₃ f₄, fibonacci_non_computable_4 n f₁ →
fibonacci_non_computable_4 (n + 1) f₂ →
fibonacci_non_computable_4 (n + 2) f₃ →
fibonacci_non_computable_4 (n + 3) f₄ →
fibonacci_non_computable_4 (n + 4) (f₁ + f₂ + f₃ + f₄)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def fib4State : Nat → Nat × Nat × Nat × Nat
| 0 => (0, 0, 2, 0)
| n+1 =>
  let s := fib4State n
  let a := s.1
  let b := s.2.1
  let c := s.2.2.1
  let d := s.2.2.2
  (b, c, d, a + b + c + d)

-- LLM HELPER
lemma fib4_state_spec (n : Nat) :
  fibonacci_non_computable_4 n (fib4State n).1 ∧
  fibonacci_non_computable_4 (n+1) (fib4State n).2.1 ∧
  fibonacci_non_computable_4 (n+2) (fib4State n).2.2.1 ∧
  fibonacci_non_computable_4 (n+3) (fib4State n).2.2.2 := by
  induction' n with n ih
  · dsimp [fib4State]
    constructor
    · exact fibonacci_non_computable_4.base0
    constructor
    · exact fibonacci_non_computable_4.base1
    constructor
    · exact fibonacci_non_computable_4.base2
    · exact fibonacci_non_computable_4.base3
  · rcases ih with ⟨h0, h1, h2, h3⟩
    constructor
    · simpa [fib4State] using h1
    constructor
    · simpa [fib4State] using h2
    constructor
    · simpa [fib4State] using h3
    ·
      have hstep : fibonacci_non_computable_4 (n + 4)
          ((fib4State n).1 + (fib4State n).2.1 + (fib4State n).2.2.1 + (fib4State n).2.2.2) :=
        fibonacci_non_computable_4.step n
          (fib4State n).1 (fib4State n).2.1 (fib4State n).2.2.1 (fib4State n).2.2.2
          h0 h1 h2 h3
      simpa [fib4State, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep
-- </vc-helpers>

-- <vc-definitions>
def implementation (n: Nat) : Nat :=
  (fib4State n).1
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(impl: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
fibonacci_non_computable_4 n result
-- program terminates
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  refine ⟨implementation n, rfl, ?_⟩
  have h := (fib4_state_spec n).1
  simpa [implementation] using h
-- </vc-theorems>

-- #test implementation 5 = 4
-- #test implementation 6 = 8
-- #test implementation 7 = 14