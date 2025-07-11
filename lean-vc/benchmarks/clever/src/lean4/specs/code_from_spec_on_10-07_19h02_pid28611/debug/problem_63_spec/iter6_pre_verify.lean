import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def fibonacci_non_computable_3 (n: Nat) (result: Nat) : Prop :=
  result = Nat.fib n

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

def implementation (n: Nat) : Nat := 
  (fib_helper n).1

-- LLM HELPER
lemma fib_helper_first (n: Nat) : (fib_helper n).1 = Nat.fib n := by
  induction n with
  | zero => 
    simp [fib_helper, Nat.fib]
  | succ n ih =>
    simp [fib_helper, Nat.fib]
    rw [ih]
    simp [fib_helper_second n]

-- LLM HELPER
lemma fib_helper_second (n: Nat) : (fib_helper n).2 = Nat.fib (n + 1) := by
  induction n with
  | zero => 
    simp [fib_helper, Nat.fib]
  | succ n ih =>
    simp [fib_helper, Nat.fib]
    rw [fib_helper_first n]
    rw [ih]

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec
  simp
  unfold fibonacci_non_computable_3
  unfold implementation
  exact fib_helper_first n