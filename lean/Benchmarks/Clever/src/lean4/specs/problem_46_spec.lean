import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Basic

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

def implementation (n: Nat) : Nat := sorry

theorem correctness
(n: Nat)
: problem_spec implementation n
:= sorry
