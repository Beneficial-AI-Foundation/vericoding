import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
  n > 0 →
    (∃ i, Nat.fib i = result ∧ Nat.Prime result ∧
      (∃! S : Finset Nat, S.card = n - 1 ∧
      (∀ y ∈ S, (∃ k, y = Nat.fib k) ∧ y < result ∧ Nat.Prime y))
    )
-- program termination
∃ result, implementation n = result ∧
spec result

def implementation (n: Nat) : Nat := sorry

theorem correctness
(n: Nat)
: problem_spec implementation n
:= sorry
