import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic

-- LLM HELPER
def fibonacci_non_computable_3 (n: Nat) (result: Nat) : Prop :=
  result = Nat.fibonacci n

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
def fib_helper : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 => 
    let (a, b) := fib_helper n
    (b, a + b)

def implementation (n: Nat) : Nat := (fib_helper n).1

-- LLM HELPER
lemma fib_helper_correct (n: Nat) : (fib_helper n).1 = Nat.fibonacci n := by
  induction n with
  | zero => simp [fib_helper, Nat.fibonacci]
  | succ n ih =>
    simp [fib_helper, Nat.fibonacci]
    rw [←ih]
    cases' fib_helper n with a b
    simp [fib_helper] at ih ⊢
    rw [ih]
    rw [Nat.fibonacci_succ_succ]
    simp

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec, fibonacci_non_computable_3, implementation]
  exact fib_helper_correct n