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

-- LLM HELPER
def fib_helper (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib_helper n + fib_helper (n + 1)

-- LLM HELPER
lemma fib_helper_eq_fib (n : Nat) : fib_helper n = Nat.fib n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
        rw [fib_helper, Nat.fib]
        rw [ih (n + 1) (Nat.lt_add_of_pos_left (by norm_num : 0 < 2))]
        rw [ih n (Nat.lt_add_of_pos_right (by norm_num : 0 < 2))]

def implementation (n: Nat) : Nat := fib_helper n

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec, implementation, fibonacci_non_computable_4]
  rw [fib_helper_eq_fib]