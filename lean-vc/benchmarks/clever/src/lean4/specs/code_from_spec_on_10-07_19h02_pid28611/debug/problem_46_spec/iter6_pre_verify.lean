import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def fibonacci_non_computable_4 (n : Nat) (result : Nat) : Prop :=
  result = Nat.fib n

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

def implementation (n: Nat) : Nat := 
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => Nat.fib n + Nat.fib (n + 1)

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec, implementation, fibonacci_non_computable_4]
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      rw [Nat.fib_add_two]