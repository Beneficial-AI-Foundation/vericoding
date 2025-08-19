import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def fibonacci_non_computable_3 (n : Nat) (result : Nat) : Prop :=
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

def implementation (n: Nat) : Nat := Nat.fib n

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec]
  use Nat.fib n
  constructor
  · rfl
  · simp [fibonacci_non_computable_3]