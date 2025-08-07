import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Basic

/-- Fibonacci function -/
def fibonacci_non_computable (n : Nat) : Nat := sorry

def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
result = fibonacci_non_computable n
-- program termination
∃ result, implementation n = result ∧
spec result

def implementation (n: Nat) : Nat := sorry

theorem correctness
(n: Nat)
: problem_spec implementation n
:= sorry
